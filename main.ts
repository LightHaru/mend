// mend - see SPEC.md
import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS=['auto','unified','search-replace','v4a','json'];
class Exit2{readonly line:string;constructor(line:string){this.line=line}}
class Fail{readonly code:string;readonly path:string;constructor(code:string,path:string){this.code=code;this.path=path}}
const blank=(s:string)=>s.trim()==='';
function patchLines(t:string):string[] {
 if(t==='')return[];
 const a=t.split('\n');if(t.endsWith('\n'))a.pop();
 return a.map(s=>s.endsWith('\r')?s.slice(0,-1):s);
}
function safe(p:string){return p!==''&&!p.startsWith('/')&&!p.includes('\\')&&p.split('/').every(s=>s!==''&&s!=='.'&&s!=='..');}
class Tree{
 private orig=new Map<string,string|null>();now=new Map<string,string|null>();moves=new Set<string>();
 original(p:string):string|null{if(!this.orig.has(p)){let v:string|null=null;try{if(statSync(p).isFile())v=readFileSync(p,'utf8')}catch{}this.orig.set(p,v)}return this.orig.get(p)!}
 get(p:string){return this.now.has(p)?this.now.get(p)!:this.original(p)}
}
type Edit=(t:Tree)=>void;
function detect(ls:string[]):string|null{
 const n=ls.findIndex(s=>!blank(s));if(n<0)return null;
 if(ls[n]!.trim()==='*** Begin Patch')return 'v4a';
 const c=ls[n]!.trimStart()[0];if(c==='['||c==='{')return 'json';
 if(ls.some(s=>s.trimEnd()==='<<<<<<< SEARCH'))return 'search-replace';
 if(ls.some((s,i)=>s.startsWith('diff --git ')||(s.startsWith('--- ')&&(ls[i+1]??'').startsWith('+++ '))))return 'unified';
 return null;
}
function jsonEdit(v:unknown):Edit|null{
 if(v===null||typeof v!=='object'||Array.isArray(v))return null;
 const o=v as Record<string,unknown>,p=o.path;if(typeof p!=='string')return null;
 const exists=(t:Tree)=>{if(!safe(p))throw new Fail('unsafe',p);const x=t.get(p);if(x===null)throw new Fail('missing',p);return x};
 if(o.command==='create'&&typeof o.file_text==='string'){const x=o.file_text;return t=>{if(!safe(p))throw new Fail('unsafe',p);if(t.get(p)!==null)throw new Fail('exists',p);t.now.set(p,x)}}
 if(o.command==='str_replace'&&typeof o.old_str==='string'&&o.old_str!==''&&(o.new_str===undefined||typeof o.new_str==='string')){
  const old=o.old_str,newS=(o.new_str as string|undefined)??'';return t=>{
   const b=exists(t),nl=b.indexOf('\n'),crlf=nl>0&&b[nl-1]==='\r';
   const lf=(s:string)=>crlf?s.replaceAll('\r\n','\n'):s;
   const text=lf(b),os=lf(old),ns=lf(newS);
   let n=0;for(let k=text.indexOf(os);k>=0;k=text.indexOf(os,k+1))n++;
   if(n===0)throw new Fail('no-match',p);if(n>1)throw new Fail('ambiguous',p);
   const k=text.indexOf(os),out=text.slice(0,k)+ns+text.slice(k+os.length);
   t.now.set(p,crlf?out.replaceAll('\n','\r\n'):out);
  }
 }
 if(o.command==='insert'&&typeof o.insert_line==='number'&&Number.isInteger(o.insert_line)&&typeof o.new_str==='string'){
  const at=o.insert_line,add=patchLines(o.new_str);return t=>{
   const b=exists(t),nl=b.indexOf('\n'),br=nl>0&&b[nl-1]==='\r'?'\r\n':'\n';
   const ls=b===''?[]:b.split(br),final=b!==''&&b.endsWith(br);if(final)ls.pop();
   if(at<0||at>ls.length)throw new Fail('no-match',p);
   ls.splice(at,0,...add);t.now.set(p,ls.length===0?'':ls.join(br)+(final?br:''));
  }
 }
 return null;
}
function jsonEdits(text:string,ls:string[]):Edit[]{
 const first=ls.findIndex(s=>!blank(s));if(first<0)throw new Exit2('error: parse 1');
 if(ls[first]!.trimStart().startsWith('[')){
  let v:unknown;try{v=JSON.parse(text)}catch{throw new Exit2(`error: parse ${first+1}`)}
  if(!Array.isArray(v))throw new Exit2(`error: parse ${first+1}`);
  return v.map(x=>{const e=jsonEdit(x);if(!e)throw new Exit2(`error: parse ${first+1}`);return e});
 }
 const out:Edit[]=[];ls.forEach((l,i)=>{if(blank(l))return;let e:Edit|null=null;try{e=jsonEdit(JSON.parse(l))}catch{}if(!e)throw new Exit2(`error: parse ${i+1}`);out.push(e)});return out;
}

interface FL{ls:string[];br:'\n'|'\r\n';final:boolean}
function fileLines(t:string):FL{
 if(t==='')return{ls:[],br:'\n',final:false};
 const nl=t.indexOf('\n'),br=nl>0&&t[nl-1]==='\r'?'\r\n':'\n',ls=t.split(br),final=t.endsWith(br);if(final)ls.pop();return{ls,br,final};
}
function joinFL(v:FL,ls:string[],final=v.final){return ls.length?ls.join(v.br)+(final?v.br:''):''}
const rt=(s:string)=>s.replace(/[ \t]+$/,''),bt=(s:string)=>rt(s.replace(/^[ \t]+/,'')),lead=(s:string)=>/^[ \t]*/.exec(s)![0];
function tm(s:string,z:number){return z===1?rt(s):z===2?bt(s):s}
function positions(f:string[],o:string[],strict:boolean,from=0,eof=false):{tier:number;p:number[]}|null{
 if(!o.length)return null;
 for(let z=0;z<3;z++){
  if(strict&&z>0)break;const p:number[]=[];
  for(let i=from;i+o.length<=f.length;i++){if(eof&&i+o.length!==f.length)continue;let ok=true;for(let j=0;j<o.length;j++)if(tm(f[i+j]!,z)!==tm(o[j]!,z)){ok=false;break}if(ok)p.push(i)}
  if(p.length)return{tier:z,p};
 }
 return null;
}
interface CI{text:string;ctx:boolean;oi:number}
function replace(f:string[],at:number,o:string[],n:CI[],tier:number){
 const F=tier===2?lead(f[at]??''):'',P=tier===2?lead(o[0]??''):'',out:string[]=[];
 for(const x of n){if(x.ctx)out.push(f[at+x.oi]!);else{let s=x.text;if(tier===2&&s!==''&&bt(s)!==''&&s.startsWith(P))s=F+s.slice(P.length);out.push(s)}}
 return [...f.slice(0,at),...out,...f.slice(at+o.length)];
}

interface UH{A:number;o:string[];n:CI[];no:boolean;noPlus:boolean}
function unified(ls:string[],strict:boolean):Edit[]{
 const out:Edit[]=[];let i=0;
 const diff=(l:string)=>l.startsWith('diff --git ');
 const pair=(k:number)=>k+1<ls.length&&ls[k]!.startsWith('--- ')&&ls[k+1]!.startsWith('+++ ');
 while(i<ls.length){
  let start=i;if(diff(ls[i]!)){if(!/^diff --git \S+ \S+$/.test(ls[i]!))throw new Exit2(`error: parse ${i+1}`);i++}else if(pair(i)){i+=2}else{if(ls[i]!.startsWith('@@'))throw new Exit2(`error: parse ${i+1}`);i++;continue}
  let j=i,op:string|null=null,np:string|null=null,ro:string|null=null,rn:string|null=null,dop:string|null=null,dnp:string|null=null,newMode=false,deleted=false,pairUsed=false;
  if(ls[start]?.startsWith('diff --git ')){const m=/^diff --git (\S+) (\S+)$/.exec(ls[start]!)!;dop=m[1]!.replace(/^a\//,'');dnp=m[2]!.replace(/^b\//,'')}
  if(pair(start)){pairUsed=true;op=ls[start]!.slice(4).split('\t')[0]!.trim().replace(/^a\//,'');np=ls[start+1]!.slice(4).split('\t')[0]!.trim().replace(/^b\//,'');j=start+2}else j=start+1;
  const hunks:UH[]=[];let header=true;
  while(j<ls.length){
   if(diff(ls[j]!))break;
   if(ls[start]!.startsWith('diff --git ')&&!header&&pair(j))break;
   if(!ls[start]!.startsWith('diff --git ')&&pair(j)&&j!==start+1)break;
   if(ls[j]!.startsWith('@@')){
    if(deleted){j++;while(j<ls.length&&!diff(ls[j]!)&&!pair(j)&&!ls[j]!.startsWith('@@'))j++;continue}
    header=false;const h=/^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(ls[j]!);if(!h)throw new Exit2(`error: parse ${j+1}`);
    const A=Number(h[1]!);j++;const o:string[]=[],n:CI[]=[];let oi=0,no=false,noPlus=false,lastRelevant=false,lastLinePlus=false;
    while(j<ls.length){
     const l=ls[j]!;if(diff(l)||pair(j)||l.startsWith('@@'))break;
     if(l===''){o.push('');n.push({text:'',ctx:true,oi:oi++});lastRelevant=true;lastLinePlus=false;no=false}
     else if(l.startsWith(' ')){const s=l.slice(1);o.push(s);n.push({text:s,ctx:true,oi:oi++});lastRelevant=true;lastLinePlus=false;no=false}
     else if(l.startsWith('-')){o.push(l.slice(1));oi++;lastRelevant=false;lastLinePlus=false;no=false}
     else if(l.startsWith('+')){n.push({text:l.slice(1),ctx:false,oi:-1});lastRelevant=true;lastLinePlus=true;no=false;noPlus=false}
     else if(l.startsWith('\\')){if(lastRelevant)no=true;if(lastLinePlus)noPlus=true;lastLinePlus=false}
     else break;
     j++;
    }
    while(o.length&&n.length&&o[o.length-1]===''&&n[n.length-1]!.ctx&&n[n.length-1]!.text===''){o.pop();n.pop()}
    hunks.push({A,o,n,no,noPlus});continue;
   }
   if(header){
    if(ls[j]!.startsWith('--- ')){if(j+1>=ls.length||!ls[j+1]!.startsWith('+++ '))throw new Exit2(`error: parse ${j+2}`);pairUsed=true;op=ls[j]!.slice(4).split('\t')[0]!.trim().replace(/^a\//,'');np=ls[j+1]!.slice(4).split('\t')[0]!.trim().replace(/^b\//,'');j+=2;continue}
    if(ls[j]!.startsWith('rename from '))ro=ls[j]!.slice(12).trim();
    else if(ls[j]!.startsWith('rename to '))rn=ls[j]!.slice(10).trim();
    else if(ls[j]!.startsWith('new file mode'))newMode=true;
    else if(ls[j]!.startsWith('deleted file mode'))deleted=true;
   }
   j++;
  }
  if(!pairUsed){if(ro!==null)op=ro;if(rn!==null)np=rn}
  if(op===null)op=dop;if(np===null)np=dnp;
  if(op===null||np===null){op=dop??'/dev/null';np=dnp??'/dev/null'}
  const OP=op,NP=np;
  out.push(t=>{
   if(OP!=='/dev/null'&&!safe(OP))throw new Fail('unsafe',OP);if(NP!=='/dev/null'&&!safe(NP))throw new Fail('unsafe',NP);
   if(newMode||OP===' /dev/null'||OP==='/dev/null'){
    if(t.get(NP)!==null)throw new Fail('exists',NP);
    const ls:string[]=[];for(const h of hunks)for(const x of h.n)if(!x.ctx)ls.push(x.text);
    const last=hunks[hunks.length-1];t.now.set(NP,ls.length?ls.join('\n')+(last?.noPlus?'':'\n'):'');
   }else if(deleted||NP===' /dev/null'||NP==='/dev/null'){if(t.get(OP)===null)throw new Fail('missing',OP);t.now.set(OP,null)}
   else{
    const b=t.get(OP);if(b===null)throw new Fail('missing',OP);
    if(OP!==NP&&t.get(NP)!==null)throw new Fail('exists',NP);
    const v=fileLines(b);let f=[...v.ls],d=0;
    for(const h of hunks){
     if(h.o.length){const m=positions(f,h.o,strict);if(!m)throw new Fail('no-match',OP);const target=h.A-1+d;let at=m.p[0]!;for(const q of m.p)if(Math.abs(q-target)<Math.abs(at-target))at=q;
      const matchedEOF=at+h.o.length>=f.length;
      f=replace(f,at,h.o,h.n,m.tier);d+=h.n.length-h.o.length;if(matchedEOF)v.final=!h.no;
     }else{const at=Math.min(h.A+d,f.length);const n=h.n.map(x=>x.text);const insertedEOF=at>=f.length;f=[...f.slice(0,at),...n,...f.slice(at)];d+=n.length;if(insertedEOF)v.final=!h.no}
    }
    const text=joinFL(v,f,v.final);if(OP!==NP){t.now.set(NP,text);t.now.set(OP,null);t.moves.add(OP+'\0'+NP)}else t.now.set(OP,text);
   }
  });i=j;
 }
 if(!out.length)throw new Exit2('error: parse 1');return out;
}

function search(ls:string[],strict:boolean):Edit[]{
 const out:Edit[]=[];let prev:string|null=null,i=0;
 while(i<ls.length){
  if(ls[i]!.trimEnd()!=='<<<<<<< SEARCH'){i++;continue}
  const sl=i+1;let sep=-1,end=-1;
  for(let k=i+1;k<ls.length;k++)if(ls[k]!.trimEnd()==='======='){sep=k;break}
  if(sep<0)throw new Exit2(`error: parse ${sl}`);
  for(let k=sep+1;k<ls.length;k++)if(ls[k]!.trimEnd()==='>>>>>>> REPLACE'){end=k;break}
  if(end<0)throw new Exit2(`error: parse ${sl}`);
  let start=0;for(let k=0;k<i;k++)if(ls[k]!.trimEnd()==='>>>>>>> REPLACE')start=k+1;
  let p=prev;
  for(let k=i-1;k>=start;k--){
   if(blank(ls[k]!))continue;const s=ls[k]!.trim();if(s.startsWith('```'))continue;p=s;break;
  }
  if(p===null||p==='')throw new Exit2(`error: parse ${sl}`);
  const P=p,old=ls.slice(i+1,sep),n=ls.slice(sep+1,end);
  out.push(t=>{
   if(!safe(P))throw new Fail('unsafe',P);
   if(!old.length){if(t.get(P)!==null)throw new Fail('exists',P);t.now.set(P,n.length?n.join('\n')+'\n':'')}
   else{const b=t.get(P);if(b===null)throw new Fail('missing',P);const v=fileLines(b),m=positions(v.ls,old,strict);if(!m)throw new Fail('no-match',P);if(m.p.length!==1)throw new Fail('ambiguous',P);
    let nn=[...n];if(m.tier===2){const F=lead(v.ls[m.p[0]!]!),Q=lead(old[0]!);nn=nn.map(s=>s!==''&&bt(s)!==''&&s.startsWith(Q)?F+s.slice(Q.length):s)}
    t.now.set(P,joinFL(v,[...v.ls.slice(0,m.p[0]!),...nn,...v.ls.slice(m.p[0]!+old.length)],v.final));
   }
  });prev=P;i=end+1;
 }
 if(!out.length)throw new Exit2('error: parse 1');return out;
}

interface VC{anchor:string|null;eof:boolean;o:string[];n:CI[]}
function v4a(ls:string[],strict:boolean):Edit[]{
 let first=-1;for(let k=0;k<ls.length;k++)if(!blank(ls[k]!)){first=k;break}
 if(first<0)throw new Exit2('error: parse 1');if(ls[first]!.trim()!=='*** Begin Patch')throw new Exit2(`error: parse ${first+1}`);
 let last=-1;for(let k=ls.length-1;k>=0;k--)if(!blank(ls[k]!)){last=k;break}
 if(last<0||ls[last]!.trim()!=='*** End Patch')throw new Exit2(`error: parse ${ls.length+1}`);
 const out:Edit[]=[];let i=first+1;
 while(i<last){
  if(blank(ls[i]!)){i++;continue}
  const l=ls[i]!;let kind='',p='';
  if(l.startsWith('*** Add File: ')){kind='add';p=l.slice(14).trim()}
  else if(l.startsWith('*** Delete File: ')){kind='delete';p=l.slice(17).trim()}
  else if(l.startsWith('*** Update File: ')){kind='update';p=l.slice(17).trim()}
  else throw new Exit2(`error: parse ${i+1}`);
  const sectionLine=i+1;i++;const section:string[]=[];
  while(i<last&&!ls[i]!.startsWith('*** Add File: ')&&!ls[i]!.startsWith('*** Delete File: ')&&!ls[i]!.startsWith('*** Update File: ')){section.push(ls[i]!);i++}
  while(section.length&&blank(section[section.length-1]!))section.pop();
  if(kind==='add'){
   const content:string[]=[];for(let k=0;k<section.length;k++){const s=section[k]!;if(s==='')content.push('');else if(s.startsWith('+'))content.push(s.slice(1));else throw new Exit2(`error: parse ${sectionLine+k+1}`)}
   const P=p;out.push(t=>{if(!safe(P))throw new Fail('unsafe',P);if(t.get(P)!==null)throw new Fail('exists',P);t.now.set(P,content.length?content.join('\n')+'\n':'')});
  }else if(kind==='delete'){
   if(section.length)throw new Exit2(`error: parse ${sectionLine+1}`);
   const P=p;out.push(t=>{if(!safe(P))throw new Fail('unsafe',P);if(t.get(P)===null)throw new Fail('missing',P);t.now.set(P,null)});
  }else{
   let move:string|null=null,si=0;if(section[0]?.startsWith('*** Move to: ')){move=section[0]!.slice(13).trim();si=1}
   const chunks:VC[]=[];let k=si;
   while(k<section.length){
    let anchor:string|null=null,eof=false;
    if(section[k]!.startsWith('@@')){anchor=section[k]!.slice(2).trim();anchor=anchor===''?null:anchor;k++}
    else if(chunks.length===0){/* first body chunk */}
    else throw new Exit2(`error: parse ${sectionLine+k}`);
    const o:string[]=[],n:CI[]=[];let oi=0;
    while(k<section.length){
     if(section[k]!.startsWith('@@'))break;     if(section[k]==='*** End of File'){eof=true;k++;break}
     const s=section[k]!;k++;
     if(s===''){o.push('');n.push({text:'',ctx:true,oi:oi++})}
     else if(s.startsWith(' ')){const x=s.slice(1);o.push(x);n.push({text:x,ctx:true,oi:oi++})}
     else if(s.startsWith('-')){o.push(s.slice(1));oi++}
     else if(s.startsWith('+'))n.push({text:s.slice(1),ctx:false,oi:-1})
     else throw new Exit2(`error: parse ${sectionLine+k}`);
    }
    chunks.push({anchor,eof,o,n});
   }
   if(!chunks.length&&move===null)throw new Exit2(`error: parse ${sectionLine}`);
   const P=p,MP=move;out.push(t=>{
    if(!safe(P))throw new Fail('unsafe',P);
    if(MP!==null&&!safe(MP))throw new Fail('unsafe',MP);
    if(t.get(P)===null)throw new Fail('missing',P);
    if(MP!==null&&t.get(MP)!==null)throw new Fail('exists',MP)
    const v=fileLines(t.get(P)!);let f=[...v.ls],cursor=0;
    for(const c of chunks){
     if(c.anchor!==null){
      let found=-1;for(let z=0;z<3;z++){if(strict&&z>0)break;for(let q=cursor;q<f.length;q++)if(tm(f[q]!,z)===tm(c.anchor,z)){found=q;break}if(found>=0)break}
      if(found<0)throw new Fail('no-match',P);cursor=found+1;
     }
     if(c.o.length){
      const m=positions(f,c.o,strict,cursor,c.eof);if(!m)throw new Fail('no-match',P);const at=m.p[0]!;f=replace(f,at,c.o,c.n,m.tier);cursor=at+c.n.length;
     }else{const at=c.eof?f.length:cursor;const n=c.n.map(x=>x.text);f=[...f.slice(0,at),...n,...f.slice(at)];cursor=at+n.length}
    }
    const text=joinFL(v,f,v.final);if(MP!==null){t.now.set(MP,text);t.now.set(P,null);t.moves.add(P+'\0'+MP)}else t.now.set(P,text);
   });
  }
 }
 if(!out.length)throw new Exit2('error: parse 1');return out;
}

function run(args:string[]):{code:number;out:string[]}{
 let format:string|null=null,check=false,strict=false;const pos:string[]=[];let ended=false;
 for(const a of args){
  if(!ended&&a==='--')ended=true;
  else if(!ended&&a.startsWith('-')&&a!=='-'){
   if(a.startsWith('--format=')&&format===null&&FORMATS.includes(a.slice(9)))format=a.slice(9);
   else if(a==='--check'&&!check)check=true;else if(a==='--strict'&&!strict)strict=true;else return{code:2,out:['error: usage']};
  }else pos.push(a);
 }
 if(pos.length>1)return{code:2,out:['error: usage']};
 const file=pos.length===0||pos[0]==='-'?null:pos[0]!;let text='';
 try{text=readFileSync(file??0,'utf8')}catch{if(file!==null)return{code:2,out:['error: no-patch']}}
 const ls=patchLines(text),kind=format===null||format==='auto'?detect(ls):format;if(kind===null)return{code:2,out:['error: format']};
 let edits:Edit[]=[];
 try{
  if(kind==='json')edits=jsonEdits(text,ls);
  else if(kind==='unified')edits=unified(ls,strict);
  else if(kind==='search-replace')edits=search(ls,strict);
  else edits=v4a(ls,strict);
 }catch(e){
  if(e instanceof Exit2)return{code:2,out:[e.line]};
  throw e;
 }
 const t=new Tree(),fails:Fail[]=[];
 for(const e of edits){const before=new Map(t.now);try{e(t)}catch(x){if(!(x instanceof Fail))throw x;t.now.clear();for(const[k,v]of before)t.now.set(k,v);fails.push(x)}
 }
 if(fails.length)return{code:1,out:[...fails.map(f=>`error: ${f.code} ${f.path}`),`failed: ${fails.length} of ${edits.length} edits`]};
 const entries:{key:string;line:string}[]=[];const keys=new Set(t.now.keys());
 for(const pair of t.moves){const[a,b]=pair.split('\0');if(t.original(a)!==null&&t.now.get(a)===null&&t.original(b)===null&&t.now.get(b)!==null){entries.push({key:b,line:`R ${a} -> ${b}`});keys.delete(a);keys.delete(b)}}
 for(const p of keys){const w=t.original(p),n=t.now.get(p)!;if(w===n)continue;entries.push({key:p,line:`${w===null?'A':n===null?'D':'M'} ${p}`})}
 entries.sort((a,b)=>Buffer.compare(Buffer.from(a.key),Buffer.from(b.key)));
 if(!check){for(const pair of t.moves){const[a,b]=pair.split('\0');if(t.original(a)!==null&&t.now.get(a)===null&&t.original(b)===null&&t.now.get(b)!==null){rmSync(a,{force:true});mkdirSync(dirname(b),{recursive:true});writeFileSync(b,t.now.get(b)!)}}
  for(const p of keys){const w=t.original(p),n=t.now.get(p)!;if(w===n)continue;if(n===null)rmSync(p,{force:true});else{mkdirSync(dirname(p),{recursive:true});writeFileSync(p,n)}}}
 const rows=entries.map(e=>e.line);return{code:0,out:[...rows,`ok: ${rows.length} ${rows.length===1?'file':'files'}`]};
}
const trialEnv=process.env.MAKEFUN_ENV_URL;
if(trialEnv!==undefined&&trialEnv!==''){const{runTrial}=await import('./runner.ts');await runTrial(trialEnv)}
else{const r=run(process.argv.slice(2));writeSync(1,r.out.map(l=>l+'\n').join(''));process.exitCode=r.code}

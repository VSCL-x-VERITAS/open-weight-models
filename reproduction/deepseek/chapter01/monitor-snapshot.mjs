import {readFileSync,writeFileSync,appendFileSync,mkdirSync} from 'node:fs';
import {dirname,join,resolve} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
const base=dirname(fileURLToPath(import.meta.url)),project=resolve(base,'../..');
const launch=JSON.parse(readFileSync(join(base,'chapter01-main-launch.json'),'utf8'));
const modules=join(project,'.tools/deepseek-harness/node_modules/@deepseek-ai');
const {Context}=await import(pathToFileURL(join(modules,'cordis/lib/index.js')));
const P=await import(pathToFileURL(join(modules,'dsh-session-persistence-jsonl/lib/index.js')));
const ctx=new Context();let snapshot;
try{
 await ctx.plugin(P,{root:join(project,'.tools/deepseek-chapter01-clean/home/sessions'),compression:'zstd',listConcurrency:3}).await();
 const h=await ctx.sessionPersistence.open(launch.session_id,'read');
 try{
  const {events}=await h.read();const starts=events.filter(e=>e.type==='turn/start');const start=starts[1];
  if(!start)throw Error('formalization_turn_not_started');
  const scope=events.filter(e=>e.seq>=start.seq);const calls=new Map(scope.filter(e=>e.type==='tool/call').map(e=>[e.data.callId,e]));
  const results=scope.filter(e=>e.type==='tool/result');let images=0;const infrastructure=[];
  const texts=m=>typeof m?.content==='string'?m.content:Array.isArray(m?.content)?m.content.filter(x=>x.type==='text').map(x=>x.text).join('\n'):'';
  for(const e of results){
   const m=e.data.message,id=m?.toolCallId??m?.source?.callId,name=calls.get(id)?.data.name??'';
   if(name==='read_image'&&!m?.isError&&!e.data.isError)images++;
   const t=texts(m);if(/EPERM:|EACCES:|sandbox_apply:|no sandbox backend is usable|ECONNREFUSED|missing_credential/i.test(t)){
    infrastructure.push({tool:name,at:new Date(e.time).toISOString(),error:t.slice(0,450)});
   }
  }
  const argsOf=e=>{let a=e.data.arguments??e.data.args??e.data.input;if(typeof a==='string'){try{a=JSON.parse(a)}catch{}}return a??{}};
  const commands=[...calls.values()].map(e=>argsOf(e).command??'').filter(x=>typeof x==='string');
  const ending=scope.filter(e=>e.type==='turn/end').at(-1);
  snapshot={observed_at:new Date().toISOString(),session_id:launch.session_id,formalization_started_at:new Date(start.time).toISOString(),elapsed_seconds:(Date.now()-start.time)/1000,
   turn_open:!ending,turn_end_reason:ending?.data.reason?.kind??null,tool_calls:calls.size,tool_results:results.length,
   source_pdf_operations:commands.filter(x=>/Chapter01[.]pdf/.test(x)).length,mathlib_search_operations:commands.filter(x=>/rg |grep |sed |cat /.test(x)&&/mathlib|Mathlib/.test(x)).length,
   compiler_operations:commands.filter(x=>/tools\/(lean|lake)[.]sh|lake (build|env)/.test(x)).length,successful_image_reads:images,infrastructure_errors:infrastructure,
   lean_files:scope.filter(e=>e.type==='tool/call'&&['write','edit'].includes(e.data.name)).map(e=>argsOf(e).file_path??argsOf(e).path??'').filter(x=>x.endsWith('.lean'))};
  if(ending){const final=scope.filter(e=>e.type==='assistant/message').at(-1);snapshot.final_response=texts(final?.data.message).slice(0,2200)}
 }finally{await h.close()}
}finally{await ctx.fiber.dispose()}
const out=join(base,'operator-monitor');mkdirSync(out,{recursive:true});
appendFileSync(join(out,'chapter01-first-five-minutes.jsonl'),JSON.stringify(snapshot)+'\n');
writeFileSync(join(out,'latest.json'),JSON.stringify(snapshot,null,2)+'\n');
console.log(JSON.stringify(snapshot,null,2));

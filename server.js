"use strict";
/**
 * Anes TEST-ONLY attendance API.
 * Server-issued anonymous, isolated per-device cookie (NOT LINE identity).
 * Read-only timecard + POST in/out, no correction/delete routes.
 * Atomically stored on Render ephemeral filesystem (NOT payroll-grade durability).
 * This is not to be connected to employee masters, GAS, production Sheets or LINE push.
 */
const http = require("node:http");
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { performance } = require("node:perf_hooks");

const PORT = Number(process.env.PORT || 10000);
const STORE = process.env.TEST_STORE_PATH || path.join("/tmp", "anes-attendance-test-v1.json");
const INDEX = path.join(__dirname, "attendance-test.html");
const COOKIE = "anes_punch_test";
const MAX_BODY = 2048;
const ACCURACY_LIMIT = 100;
const MAX_GPS_AGE = 60000;
const RETENTION_LIMIT = 30000;
const DATE_FORMAT = new Intl.DateTimeFormat("en-US", {
  timeZone:"Asia/Tokyo", year:"numeric",month:"2-digit",day:"2-digit",
  hour:"2-digit",minute:"2-digit",hour12:false,hourCycle:"h23"
});
const jsonHeaders = {"Content-Type":"application/json; charset=utf-8","Cache-Control":"no-store"};
let db;

function nowInJST(iso){
 const map={};
 for(const t of DATE_FORMAT.formatToParts(new Date(iso))){if(t.type!=="literal")map[t.type]=t.value;}
 return {day:map.year+"-"+map.month+"-"+map.day,time:map.hour+":"+map.minute};
}
function fromDisk(){
 try{
  const d=JSON.parse(fs.readFileSync(STORE,"utf8"));
  if(d.v===1&&d.sessions&&Array.isArray(d.records))return d;
 }catch(e){if(e.code!=="ENOENT")console.error("test_store_read_failure",e.code||"error");}
 return {v:1,nextId:1,sessions:{},records:[]};
}
db=fromDisk();
function persist(){
 fs.mkdirSync(path.dirname(STORE),{recursive:true,mode:0o700});
 const temp=STORE+"."+process.pid+".tmp";
 const fd=fs.openSync(temp,"w",0o600);
 try{
  fs.writeFileSync(fd,JSON.stringify(db));
  fs.fsyncSync(fd);
 } finally {fs.closeSync(fd);}
 fs.renameSync(temp,STORE);
}
function security(res){
 res.setHeader("X-Content-Type-Options","nosniff");
 res.setHeader("Referrer-Policy","no-referrer");
 res.setHeader("X-Frame-Options","DENY");
 res.setHeader("Cache-Control","no-store");
 res.setHeader("Permissions-Policy","geolocation=(self), camera=(), microphone=()");
 res.setHeader("Content-Security-Policy","default-src 'none'; script-src 'self' 'unsafe-inline' https://static.line-scdn.net; style-src 'self' 'unsafe-inline'; connect-src 'self' https://api.line.me; img-src 'self' data:; base-uri 'none'; form-action 'none'; frame-ancestors 'none'");
}
function reply(res,status,obj,additional={}){
 res.writeHead(status,{...jsonHeaders,...additional});
 res.end(JSON.stringify(obj));
}
function noWriteResponse(res){reply(res,405,{ok:false,message:"この操作は許可されていません。"}, {"Allow":"GET, POST"});}
function parseCookies(header){
 const out={};
 for(const c of String(header||"").split(";")){
  const p=c.indexOf("=");if(p>0)out[c.slice(0,p).trim()]=c.slice(p+1).trim();
 }
 return out;
}
function hash(t){return crypto.createHash("sha256").update(t).digest("hex");}
function session(req,res,{create=false}={}){
 const token=parseCookies(req.headers.cookie)[COOKIE]||"";
 if(/^[a-f0-9]{64}$/.test(token)){
  const h=hash(token);
  if(db.sessions[h])return h;
 }
 if(!create)return null;
 if(Object.keys(db.sessions).length>2500)throw Object.assign(new Error("session_limit"),{code:"SESSION_LIMIT"});
 const t=crypto.randomBytes(32).toString("hex"), h=hash(t);
 db.sessions[h]={createdAt:new Date().toISOString()};
 persist();
 res.setHeader("Set-Cookie",COOKIE+"="+t+"; Path=/; Max-Age=604800; HttpOnly; Secure; SameSite=Lax");
 return h;
}
function findLast(h){
 for(let i=db.records.length-1;i>=0;i--)if(db.records[i].session===h)return db.records[i];
 return null;
}
function responseRecord(r){
 const jst=nowInJST(r.serverAt);
 return {id:r.id,type:r.type,serverAt:r.serverAt,date:jst.day,time:jst.time,
  accuracyM:r.accuracyM,geoFlag:r.geoFlag,distanceM:r.distanceM??null};
}
function haversine(lat1,lon1,lat2,lon2){
 const r=Math.PI/180;const a=Math.sin((lat2-lat1)*r/2)**2+
  Math.cos(lat1*r)*Math.cos(lat2*r)*Math.sin((lon2-lon1)*r/2)**2;
 return Math.round(6371000*2*Math.asin(Math.min(1,Math.sqrt(a))));
}
function geofence(lat,lng){
 let parsed;
 try{parsed=JSON.parse(process.env.TEST_SITES_JSON||"[]");}catch{return{geoFlag:"判定未設定",distanceM:null};}
 if(!Array.isArray(parsed)||!parsed.length)return{geoFlag:"判定未設定",distanceM:null};
 const sites=parsed.filter(x=>typeof x.name==="string"&&Number.isFinite(x.lat)&&Number.isFinite(x.lng) &&
  Number.isFinite(x.radiusM)&&x.radiusM>0);
 if(!sites.length)return{geoFlag:"判定未設定",distanceM:null};
 const closest=sites.map(x=>({name:x.name,distanceM:haversine(lat,lng,x.lat,x.lng),radius:x.radiusM}))
    .sort((a,b)=>a.distanceM-b.distanceM)[0];
 return{geoFlag:closest.distanceM<=closest.radius?"院内":"要確認",distanceM:closest.distanceM};
}
function isSameOrigin(req){
 const origin=req.headers.origin||"";
 const host=req.headers.host||"";
 return origin==="https://"+host ||
   (process.env.NODE_ENV==="test"&&origin==="http://"+host);
}
function validPosition(p,serverNow){
 if(typeof p!=="object"||!p)return false;
 const lat=p.latitude,lng=p.longitude,accuracy=p.accuracy,fixTime=p.measuredAt;
 if(![lat,lng,accuracy,fixTime].every(Number.isFinite))return false;
 if(lat< -90||lat>90||lng< -180||lng>180||accuracy<=0||accuracy>ACCURACY_LIMIT)return false;
 if(fixTime>serverNow+15000||serverNow-fixTime>MAX_GPS_AGE)return false;
 return true;
}
async function readBody(req){
 return new Promise((resolve,reject)=>{
  let text="";
  req.on("data",d=>{
   text+=d.toString("utf8");
   if(Buffer.byteLength(text)>MAX_BODY){reject(Object.assign(new Error("large_body"),{status:413}));req.destroy();}
  });
  req.on("end",()=>{
   try{resolve(JSON.parse(text));}catch{reject(Object.assign(new Error("invalid_json"),{status:400}));}
  });
  req.on("error",reject);
 });
}
function shouldBlock(req,res){
 if(!isSameOrigin(req)) {reply(res,403,{ok:false,message:"接続元を確認できません。"});return true;}
 if(!String(req.headers["content-type"]||"").startsWith("application/json")){
  reply(res,415,{ok:false,message:"送信形式が正しくありません。"});return true;
 }
 return false;
}

const server=http.createServer(async(req,res)=>{
 const started=performance.now(),received=new Date(),receivedMs=received.getTime();
 security(res);
 let url;
 try{url=new URL(req.url||"/","https://"+(req.headers.host||"localhost"));}catch{reply(res,400,{ok:false,message:"URLが不正です。"});return;}
 const endpoint=url.pathname;
 if(req.method==="GET"&&(endpoint==="/"||endpoint==="/index.html")){
  try{res.writeHead(200,{"Content-Type":"text/html; charset=utf-8","Cache-Control":"no-store"});
   res.end(fs.readFileSync(INDEX));}catch{reply(res,500,{ok:false,message:"画面を表示できません。"});}
  return;
 }
 if(req.method==="GET"&&endpoint==="/health"){
  reply(res,200,{ok:true,service:"anes-attendance-TEST",storage:"ephemeral-atomic-file",payroll:false});
  return;
 }
 if(req.method==="GET"&&endpoint==="/api/state"){
  try{
   const h=session(req,res,{create:true});
   const last=findLast(h);
   const receipt=last?responseRecord(last):null;
   reply(res,200,{ok:true,testOnly:true,displayName:"本人テスト",
      nextAction:last&&last.type==="出勤"?"退勤":"出勤",
      last:receipt,
      noPayroll:true,storageNotice:"試験用の記録です。サービス再起動時に消去される場合があります。",
      serverTime:received.toISOString(),elapsedMs:Math.round(performance.now()-started)});
  }catch(e){console.error("test_bootstrap_failed",e.code||"error");reply(res,503,{ok:false,message:"試験用保存先に接続できません。"});}
  return;
 }
 if(req.method==="GET"&&endpoint==="/api/timecard"){
  const h=session(req,res,{create:false});
  if(!h){reply(res,401,{ok:false,message:"画面を開き直してください。"});return;}
  const month=url.searchParams.get("month")||nowInJST(received.toISOString()).day.slice(0,7);
  if(!/^\d{4}-(0[1-9]|1[0-2])$/.test(month)){reply(res,400,{ok:false,message:"年月が不正です。"});return;}
  const punches=db.records.filter(r=>r.session===h&&nowInJST(r.serverAt).day.startsWith(month))
    .slice(-200).map(responseRecord);
  reply(res,200,{ok:true,month,records:punches,days:
    [...new Set(punches.map(p=>p.date))].length,noPayroll:true});
  return;
 }
 if(req.method==="GET"&&endpoint==="/api/receipt"){
  const h=session(req,res,{create:false});
  if(!h){reply(res,401,{ok:false,message:"画面を開き直してください。"});return;}
  const id=url.searchParams.get("requestId")||"";
  if(!/^[a-zA-Z0-9_-]{12,95}$/.test(id)){reply(res,400,{ok:false,message:"確認IDが不正です。"});return;}
  const r=db.records.find(x=>x.session===h&&x.requestId===id);
  reply(res,200,{ok:true,saved:!!r,record:r?responseRecord(r):null});
  return;
 }
 if(req.method==="POST"&&endpoint==="/api/punch"){
  if(shouldBlock(req,res))return;
  const h=session(req,res,{create:false});
  if(!h){reply(res,401,{ok:false,message:"もう一度ページを開いてください。"});return;}
  let data;
  try{data=await readBody(req)}catch(e){if(!res.writableEnded)reply(res,e.status||400,{ok:false,message:"送信内容が正しくありません。"});return;}
  if(!data||!["出勤","退勤"].includes(data.type)||
      typeof data.requestId!=="string"||!/^[a-zA-Z0-9_-]{12,95}$/.test(data.requestId)||
      !validPosition(data,receivedMs)){
   reply(res,400,{ok:false,message:"GPSの精度・取得時刻が確認できません。位置情報を再取得してください。"});
   return;
  }
  try{
   const prior=db.records.find(x=>x.session===h&&x.requestId===data.requestId);
   if(prior){
    reply(res,200,{ok:true,duplicate:true,record:responseRecord(prior),
      nextAction:prior.type==="出勤"?"退勤":"出勤"});
    return;
   }
   const last=findLast(h),next=last&&last.type==="出勤"?"退勤":"出勤";
   if(next!==data.type){
    reply(res,409,{ok:false,message:"打刻状態が更新されています。画面を再読み込みしてください。",
      nextAction:next});
    return;
   }
   const today=nowInJST(received.toISOString()).day;
   const todayCount=db.records.filter(x=>x.session===h&&nowInJST(x.serverAt).day===today).length;
   if(todayCount>=20){
    reply(res,429,{ok:false,message:"テスト打刻回数の上限に達しました。"});return;
   }
   if(db.records.length>RETENTION_LIMIT){reply(res,503,{ok:false,message:"試験用記録の上限です。"});return;}
   const loc=geofence(data.latitude,data.longitude);
   const rec={
    id:db.nextId++,session:h,requestId:data.requestId,type:data.type,
    serverAt:received.toISOString(),latitude:data.latitude,longitude:data.longitude,
    accuracyM:Math.round(data.accuracy),measuredAt:new Date(data.measuredAt).toISOString(),
    geoFlag:loc.geoFlag,distanceM:loc.distanceM
   };
   db.records.push(rec);
   try{persist();}
   catch(e){db.records.pop();db.nextId--;throw e;}
   res.setHeader("Server-Timing","save;dur="+(performance.now()-started).toFixed(1));
   reply(res,201,{ok:true,record:responseRecord(rec),
    nextAction:rec.type==="出勤"?"退勤":"出勤",
    saveMs:Math.round(performance.now()-started),storage:"test_only_ephemeral"});
  }catch(e){console.error("test_punch_commit_error",e.code||"error");reply(res,503,{ok:false,message:"保存を確認できません。再送せず確認してください。"});}
  return;
 }
 if(["PATCH","DELETE","PUT"].includes(req.method)){noWriteResponse(res);return;}
 reply(res,404,{ok:false,message:"ページがありません。"});
});
server.listen(PORT,"0.0.0.0",()=>console.log("Anes TEST-only punch app listening",PORT));

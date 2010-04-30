/* -*- Mode: Javascript; -*- */

/* Copyright (C) 2009-2010 beingmeta, inc.
   This file provides a Javascript/ECMAScript of KNOWLETS, 
     a lightweight knowledge representation facility.

   For more information on knowlets, visit www.knowlets.net
   For more information about beingmeta, visit www.beingmeta.com

   This library is built on the FDJT (www.fdjt.org) toolkit.

   This program comes with absolutely NO WARRANTY, including implied
   warranties of merchantability or fitness for any particular
   purpose.

    Use, modification and redistribution of this program is permitted
    under the GNU General Public License (GPL) Version 2:

          http://www.gnu.org/licenses/old-licenses/gpl-2.0.html

    Use and redistribution (especially embedding in other
      CC licensed content) is permitted under the terms of the
      Creative Commons "Attribution-NonCommercial" license:

          http://creativecommons.org/licenses/by-nc/3.0/ 

    Other uses may be allowed based on prior agreement with
      beingmeta, inc.  Inquiries can be addressed to:

       licensing@biz.beingmeta.com

   Enjoy!

*/

var Knowlet=
  (function(){
    var knowlets={};
    var all_knowlets=[];
    var knowlet=false;
    var trace_parsing=0;
    var trace_edits=false;

    var kno_simple_oidpat=/@[0-9A-Fa-f]+\/[0-9A-Fa-f]+/;
    var kno_named_oidpat=/@[0-9A-Fa-f]+\/[0-9A-Fa-f]+(\x22([^\x22]+)\x22)*/;
    var kno_atbreak=/[^\\]@/g;
    
    function Knowlet(id,lang) {
      // Raw cons
      if (!(id)) return this;
      // Do lookup
      if (knowlets[id])
	if ((lang)&&(lang!==knowlets[id].language))
	  throw { error: "language mismatch" };
	else return knowlets[id];
      if (fdjtKB.Pool.probe(id))
	throw { error: "pool/knowlet conflict"};
      if (this instanceof Knowlet)
	knowlet=fdjtKB.Pool.call(this,id);
      else knowlet=fdjtKB.Pool.call((new Knowlet()),id);
      // The name of the knowlet
      knowlet.name=id;
      knowlets[id]=knowlet;
      // The default language for this knowlet
      if (lang) knowlet.language=lang.toUpperCase();
      else knowlet.language='EN';
      // Mapping strings to DTerm objects (many-to-one)
      knowlet.dterms={};
      // A vector of all dterms local to this knowlet
      knowlet.alldterms=[];
      // Prime dterms
      knowlet.prime=[];
      // Whether the knowlet is indexed (e.g. keeps inverse indices for
      // relations and rules)
      knowlet.index=fdjtKB.Index();
      // Whether to validate asserted relations
      knowlet.validate=true;
      // Whether the knowlet is 'strict'
      // (requiring dterm definitions for all references)
      knowlet.strict=false;
      // Whether the knowlet is 'finished' (all references declared)
      knowlet.finished=false;
      // Terms which are assumed unique.  This is used in non-strict
      // knowlets to catch terms that become ambiguous.
      knowlet.assumed_dterms=[];
      // Mapping external dterms to knowdes
      knowlet.xdterms={};
      // A vector of all foreign references
      knowlet.allxdterms=[];
      // Mapping terms to arrays of of DTerms (ambiguous)
      knowlet.terms={};
      // Mapping hook terms to arrays of of DTerms (ambiguous)
      knowlet.hooks={};
      // Inverted indices
      knowlet.genlsIndex={};
      // This maps external OIDs to knowdes
      knowlet.oidmap={};
      // Key concepts
      knowlet.key_concepts=[];
      // DRULES (disambiguation rules)
      knowlet.drules={};
      return knowlet;}
    Knowlet.prototype=new fdjtKB.Pool();

    function DTerm(knowlet,string,lang){
      if (!(knowlet)) return this;
      if (string.search(/[a-zA-Z]\$/)===0) {
	lang=string.slice(0,2).toUpperCase();
	string=string.slice(3);}
      else if (lang) lang=lang.toUpperCase();
      else lang=knowlet.language;
      var term=string;
      if (knowlet.language!==lang) term=lang+"$"+string;
      if (knowlet.dterms.hasOwnProperty(term))
	return knowlet.dterms[term];
      var dterm=((this instanceof DTerm)?
		 (knowlet.ref(string+"@"+knowlet.name,this)):
		 (knowlet.ref(string+"@"+knowlet.name,new DTerm())));
      dterm.dterm=term; knowlet.dterms[term]=dterm;
      knowlet.alldterms.push(dterm);
      if ((lang)&&(lang!==knowlet.language)) dterm.language=lang;
      dterm._always=fdjtKB.Set();
      dterm.knowlet=knowlet;
      dterm.addTerm(string,lang);
      return dterm;}
    DTerm.prototype=new fdjtKB.KNode();

    Knowlet.DTerm=DTerm;
    Knowlet.prototype.cons=DTerm;
    Knowlet.prototype.DTerm=function(string,lang) {
      return DTerm(this,string,lang);};
    Knowlet.prototype.probe=function(string,langid) {
      if (this.language===langid)
	return this.dterms[string]||false;
      else return this.dterms[langid+"$"+string]||false;};
    
    DTerm.prototype.add=function(prop,val){
      if ((fdjtKB.KNode.prototype.add.call(this,prop,val))&&
	  (prop==='genls')) {
	fdjtKB.add(this._always,val);
	fdjtKB.merge(this._always,val._always);
	return true;}
      else return false;}
    DTerm.prototype.addTerm=function(val,field){
      if (val.search(/[a-zA-Z]\$/)===0)
	if (field)
	  this.add(val.slice(0,2)+'$'+field,val.slice(3));
	else this.add(val.slice(0,2),val.slice(3));
      else if (field) this.add(field,val);
      else this.add(this.knowlet.language,val);};
    DTerm.prototype.tagString=function(kno) {
      if ((kno===this.knowlet)||(!(kno))) return this.dterm;
      else return this.dterm+"@"+this.knowlet.name;};
    /* Text processing utilities */
    function stdspace(string) {
      return string.replace(/\s+/," ").
	replace(/^\s/,"").replace(/\s$/,"");}
    
    function trimspace(string) {
      return string.replace(/^\s/,"").replace(/\s$/,"");}

    function findBreak(string,brk,start) {
      var pos=string.indexOf(brk,start||0);
      while (pos>0)
	if (string[pos-1]!="\\")
	  return pos;
	else pos=string.indexOf(brk,pos+1);
      return pos;}

    var _knowlet_oddpat=/(\\)|(\s\s)|(\s;)|(\s;)/g;
    
    function segmentString(string,brk,start,keepspace) {
      if (start)
	if (string.slice(start).search(_knowlet_oddpat)<0)
	  return string.slice(start).split(brk);
	else {}
      else if (string.search(_knowlet_oddpat)<0)
	return string.split(brk);
      else {}
      var result=[]; var i=0, pos=start||0;
      var nextpos=findBreak(string,brk,pos);
      while (nextpos>=0) {
	var item=((keepspace) ? (string.slice(pos,nextpos)) :
		  (stdspace(string.slice(pos,nextpos))));
	if ((item) && (item !== "")) result.push(item);
	pos=nextpos+1;
	nextpos=findBreak(string,brk,pos);}
      result.push(string.slice(pos));
      return result;}
    function stripComments(string) {
      return string.replace(/^\s*#.*$/g,"").
	replace(/^\s*\/\/.*$/g,"");}

    /* Processing the PLAINTEXT microformat */
    function handleClause(clause,subject) {
      if (clause.indexOf('\\')>=0) clause=fdjtString.unEscape(clause);
      if (trace_parsing>2)
	fdjtLog("[%fs] Handling clause '%s' for %o",fdjtET(),clause,subject);
      switch (clause[0]) {
      case '^':
	if (clause[1]==='~') 
	  subject.add('sometimes',this.DTerm(clause.slice(2)));
	else if (clause[2]==='*') 
	  subject.add('commonly',this.DTerm(clause.slice(2)));
	else {
	  var pstart=findBreak("(");
	  if (pstart>0) {
	    var pend=findBreak(")",pstart);
	    if (pend<0) {
	      fdjtWarn("Invalid Knowlet clause '%s' for %o (%s)",
		       clause,subject,subject.dterm);}
	    else {
	      var role=this.DTerm(clause.slice(1,pstart));
	      var object=this.DTerm(clause.slice(pstart+1,pend));
	      object.add(role.dterm,subject);
	      subject.add('genls',role);}}
	  else subject.add('genls',this.DTerm(clause.slice(1)));}
	break;
      case '_': {
	var object=this.DTerm(clause.slice(1));
	subject.add('examples',object);
	object.add('genls',subject);
	break;}
      case '-':
	subject.add('never',this.DTerm(clause.slice(1)));
	break;
      case '&': {
	var value=clause.slice((clause[1]==="-") ? (2) : (1));
	var assoc=this.DTerm(value);
	if (clause[1]==="-")
	  subject.add('antiassocs',assoc);
	else subject.add('assocs',assoc);
	break;}
      case '@': 
	if (clause[1]==="#") 
	  subject.add('tags',clause.slice(2));
	else subject.add('uri',clause.slice(1));
	break;
      case '=':
	if (clause[1]==='@')
	  subject.oid=clause.slice(1);
	else if (clause[1]==='*')
	  subject.add('equiv',this.DTerm(clause.slice(2)));
	else if (clause[1]==='~')
	  subject.add('kinda',this.DTerm(clause.slice(2)));
	else 
	  subject.add('identical',this.DTerm(clause.slice(1)));
	break;
      case '"': {
	var qend=((clause[-1]==='"') ? (-1) : (false));
	var gloss=((qend)?(clause.slice(2,qend)):(clause.slice(2)));
	if (clause[1]==="*") {
	  subject.gloss=gloss.slice(1);
	  subject.addTerm(subject.gloss,'glosses');}
	else {
	  subject.addTerm(gloss,"glosses");}
	break;}
      case '%': {
	var mirror=this.DTerm(clause.slice(1));
	if (subject.mirror===mirror) break;
	else {
	  var omirror=subject.mirror;
	  fdjtWarn("Inconsistent mirrors for %s: +%s and -%s",
		   subject,mirror,omirror);
	  omirror.mirror=false;}
	if (mirror.mirror) {
	  var oinvmirror=mirror.mirror;
	  fdjtWarn("Inconsistent mirrors for %s: +%s and -%s",
		   mirror,subject,oinvmirror);
	  omirror.mirror=false;}
	subject.mirror=mirror; mirror.mirror=subject;
	break;}
      case '.': {
	var brk=findBreak(clause,'=');
	if (!(brk))
	  throw {name: 'InvalidClause', irritant: clause};
	var role=this.DTerm(clause.slice(1,brk));
	var object=this.DTerm(clause.slice(brk+1));
	this.add(role.dterm,object);
	object.add('genls',role);
	break;}
      default: {
	var brk=findBreak(clause,'=');
	if (brk>0) {
	  var role=this.DTerm(clause.slice(0,brk));
	  var object=this.DTerm(clause.slice(brk+1));
	  subject.add(role.dterm,object);
	  object.add('genls',role);}
	else subject.addTerm(clause);}}
      return subject;}
    Knowlet.prototype.handleClause=handleClause;

    function handleSubjectEntry(entry){
      var clauses=segmentString(entry,"|");
      var subject=this.DTerm(clauses[0]);
      if (Knowlet.trace_parsing>2)
	fdjtLog("[%fs] Processing subject entry %s %o %o",
		fdjtET(),entry,subject,clauses);
      var i=1; while (i<clauses.length)
		 this.handleClause(clauses[i++],subject);
      if (Knowlet.trace_parsing>2)
	fdjtLog("[%fs] Processed subject entry %o",fdjtET(),subject);
      return subject;}
    Knowlet.prototype.handleSubjectEntry=handleSubjectEntry;

    function handleEntry(entry){
      entry=trimspace(entry);
      if (entry.length===0) return false;
      var bar=fdjtFindSplit(entry,'|');
      var atsign=fdjtFindSplit(entry,'@');
      if ((atsign>0) && ((bar<0)||(atsign<bar))) {
	var term=entry.slice(0,atsign);
	var knostring=((bar<0) ? (entry.slice(atsign+1)) :
		       (entry.slice(atsign+1,bar)));
	var knowlet=Knowlet(knostring);
	if (bar<0) return knowlet.DTerm(term);
	else return knowlet.handleEntry(term+entry.slice(bar));}
      switch (entry[0]) {
      case '*': {
	var subject=this.handleSubjectEntry(entry.slice(1));
	if (fdjtIndexOf(this.key_concepts,subject)<0)
	  this.key_concepts.push(subject);
	return subject;}
      case '-': {
	var subentries=segmentString(entry.slice(1),"/");
	var knowdes=[];
	var i=0; while (i<subentries.length) {
	  knowdes[i]=this.DTerm(subentries[i]); i++;}
	var j=0; while (j<knowdes.length) {
	  var k=0; while (k<knowdes.length) {
	    if (j!=k) knowdes[j].add('disjoin',knowdes[k]);
	    k++;}
	  j++;}
	return knowdes[0];}
      case '/': {
	var pos=1; var subject=false; var head=false;
	var next=findBreak(entry,'/',pos);
	while (true) {
	  var basic_level=false;
	  if (entry[pos]==='*') {basic_level=true; pos++;}
	  var next_subject=
	    ((next) ? (this.handleSubjectEntry(entry.slice(pos,next))) :
	     (this.handleSubjectEntry(entry.slice(pos))));
	  if (subject) subject.add('genls',next_subject);
	  else head=next_subject;
	  subject=next_subject;
	  if (basic_level) subject.basic=true;
	  if (next) {
	    pos=next+1; next=findBreak(entry,"/",pos);}
	  else break;}
	return head;}
      default:
	return this.handleSubjectEntry(entry);}}
    Knowlet.prototype.handleEntry=handleEntry;

    function handleEntries(block){
      if (typeof block === "string") {
	var nocomment=stripComments(block);
	var segmented=segmentString(nocomment,';');
	if (Knowlet.trace_parsing>1)
	  fdjtLog("[%fs] Handling %d entries",fdjtET(),segmented.length);
	return this.handleEntries(segmented);}
      else if (block instanceof Array) {
	var results=[];
	var i=0; while (i<block.length) {
	  results[i]=this.handleEntry(block[i]); i++;}
	return results;}
      else throw {name: 'TypeError', irritant: block};}
    Knowlet.prototype.handleEntries=handleEntries;

    Knowlet.prototype.def=handleSubjectEntry;

    Knowlet.def=function(string,kno){
      if (!(kno)) kno=Knowlet.knowlet;
      return kno.def(string);};

    Knowlet.trace_parsing=0;

    return Knowlet;})();

var DTerm=Knowlet.DTerm;

function KnowletIndex(knowlet) {
  if (knowlet) this.knowlet=knowlet;
  this.byweight={}; this.bykey={}; this.tagweights={};
  return this;}

KnowletIndex.prototype.add=function(item,key,weight,kno){
  if ((weight)&&(!(this.byweight[weight])))
    this.byweight[weight]={};
  if (this.bykey[key]) fdjtKB.add(this.bykey[key],item);
  else this.bykey[key]=fdjtKB.Set(item);
  if (weight) {
    var byweight=this.byweight[weight];
    if (byweight[key]) fdjtKB.add(byweight[key],item);
    else byweight[key]=fdjtKB.Set(item);
    (this.tagweights[key])=((this.tagweights[key])||0)+weight;}
  if (kno) {
    var dterm=kno.probe(key);
    if ((dterm)&&(dterm._always)) {
      var always=dterm._always;
      var i=0; var len=always.length;
      while (i<len) this.add(item,always[i++].dterm,((weight)&&(weight-1)));}}};
KnowletIndex.prototype.freq=function(key){
  if (this.bykey[key])
    return this.bykey[key].length;
  else return 0;};
KnowletIndex.prototype.find=function(key){
  if (this.bykey[key]) return this.bykey[key];
  else return [];};
KnowletIndex.prototype.score=function(key,scores){
  var byweight=this.byweight;
  if (!(scores)) scores={};
  for (weight in byweight)
    if (byweight[weight][key]) {
      var hits=byweight[weight][key];
      var i=0; var len=hits.length;
      while (i<len) {
	var item=hits[i++]; var cur;
	if (cur=scores[item]) scores[item]=cur+weight;
	else scores[item]=weight;}}
  return scores;};



/* Emacs local variables
;;;  Local variables: ***
;;;  compile-command: "cd ..; make" ***
;;;  End: ***
*/

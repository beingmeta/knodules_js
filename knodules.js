/* -*- Mode: Javascript; -*- */

/* Copyright (C) 2009-2010 beingmeta, inc.
   This file provides a Javascript/ECMAScript of KNODULES, 
     a lightweight knowledge representation facility.

   For more information on knodules, visit www.knodules.net
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

var Knodule=
    (function(){
	var knodules={};
	var all_knodules=[];
	var knodule=false;
	var trace_parsing=0;
	var trace_edits=false;

	var kno_simple_oidpat=/@[0-9A-Fa-f]+\/[0-9A-Fa-f]+/;
	var kno_named_oidpat=/@[0-9A-Fa-f]+\/[0-9A-Fa-f]+(\x22([^\x22]+)\x22)*/;
	var kno_atbreak=/[^\\]@/g;
	
	function Knodule(id,lang) {
	    // Raw cons
	    if (!(id)) return this;
	    // Do lookup
	    if (knodules[id])
		if ((lang)&&(lang!==knodules[id].language))
		    throw { error: "language mismatch" };
	    else return knodules[id];
	    if (fdjtKB.Pool.probe(id))
		throw { error: "pool/knodule conflict"};
	    if (this instanceof Knodule)
		knodule=fdjtKB.Pool.call(this,id);
	    else knodule=fdjtKB.Pool.call((new Knodule()),id);
	    // The name of the knodule
	    knodule.name=id;
	    knodules[id]=knodule;
	    // The default language for this knodule
	    if (lang) knodule.language=lang.toUpperCase();
	    else knodule.language='EN';
	    // Mapping strings to KNode objects (many-to-one)
	    knodule.dterms={};
	    // A vector of all dterms local to this knodule
	    knodule.alldterms=[];
	    // Prime dterms
	    knodule.prime=[];
	    // Whether the knodule is indexed (e.g. keeps inverse indices for
	    // relations and rules)
	    knodule.index=fdjtKB.Index();
	    // Whether to validate asserted relations
	    knodule.validate=true;
	    // Whether the knodule is 'strict'
	    // (requiring dterm definitions for all references)
	    knodule.strict=false;
	    // Whether the knodule is 'finished' (all references declared)
	    knodule.finished=false;
	    // Terms which are assumed unique.  This is used in non-strict
	    // knodules to catch terms that become ambiguous.
	    knodule.assumed_dterms=[];
	    // Mapping external dterms to knowdes
	    knodule.xdterms={};
	    // A vector of all foreign references
	    knodule.allxdterms=[];
	    // Mapping terms to arrays of of KNodes (ambiguous)
	    knodule.terms={};
	    // Mapping hook terms to arrays of of KNodes (ambiguous)
	    knodule.hooks={};
	    // Inverted indices
	    knodule.genlsIndex={};
	    // This maps external OIDs to knowdes
	    knodule.oidmap={};
	    // Key concepts
	    knodule.key_concepts=[];
	    // DRULES (disambiguation rules)
	    knodule.drules={};
	    return knodule;}
	Knodule.prototype=new fdjtKB.Pool();
	Knodule.revid="$Id$";
	Knodule.version=parseInt("$Revision$".slice(10,-1));

	function KNode(knodule,string,lang){
	    if (!(knodule)) return this;
	    if (string.search(/[a-zA-Z]\$/)===0) {
		lang=string.slice(0,2).toUpperCase();
		string=string.slice(3);}
	    else if (lang) lang=lang.toUpperCase();
	    else lang=knodule.language;
	    var term=string;
	    if (knodule.language!==lang) term=lang+"$"+string;
	    if (knodule.dterms.hasOwnProperty(term))
		return knodule.dterms[term];
	    var dterm=((this instanceof KNode)?
		       (knodule.ref(string+"@"+knodule.name,this)):
		       (knodule.ref(string+"@"+knodule.name)));
	    dterm.dterm=term;
	    knodule.dterms[dterm.qid]=dterm;
	    knodule.dterms[term]=dterm;
	    knodule.alldterms.push(dterm);
	    if ((lang)&&(lang!==knodule.language)) dterm.language=lang;
	    dterm._always=fdjtKB.Set();
	    dterm.knodule=knodule;
	    dterm.addTerm(string,lang);
	    return dterm;}
	KNode.prototype=new fdjtKB.Ref();

	Knodule.KNode=KNode;
	Knodule.prototype.KNode=function(string,lang) {
	    return new KNode(this,string,lang);};
	Knodule.prototype.cons=function(string,lang) {
	    return new KNode(this,string,lang);};
	Knodule.prototype.probe=function(string,langid) {
	    if ((this.language===langid)||(!(langid)))
		return this.dterms[string]||false;
	    else return this.dterms[langid+"$"+string]||false;};
	
	KNode.prototype.add=function(prop,val){
	    if ((fdjtKB.Ref.prototype.add.call(this,prop,val))&&
		(prop==='genls')) {
		fdjtKB.add(this._always,val);
		fdjtKB.merge(this._always,val._always);
		return true;}
	    else return false;}
	KNode.prototype.addTerm=function(val,field){
	    if (val.search(/[a-zA-Z]\$/)===0)
		if (field)
		    this.add(val.slice(0,2)+'$'+field,val.slice(3));
	    else this.add(val.slice(0,2),val.slice(3));
	    else if (field) this.add(field,val);
	    else this.add(this.knodule.language,val);};
	KNode.prototype.tagString=function(kno) {
	    if ((kno===this.knodule)||(!(kno))) return this.dterm;
	    else return this.dterm+"@"+this.knodule.name;};
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

	var _knodule_oddpat=/(\\)|(\s\s)|(\s;)|(\s;)/g;
	
	function segmentString(string,brk,start,keepspace) {
	    if (start)
		if (string.slice(start).search(_knodule_oddpat)<0)
		    return string.slice(start).split(brk);
	    else {}
	    else if (string.search(_knodule_oddpat)<0)
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
		    subject.add('sometimes',this.KNode(clause.slice(2)));
		else if (clause[2]==='*') 
		    subject.add('commonly',this.KNode(clause.slice(2)));
		else {
		    var pstart=findBreak("(");
		    if (pstart>0) {
			var pend=findBreak(")",pstart);
			if (pend<0) {
			    fdjtLog.warn("Invalid Knodule clause '%s' for %o (%s)",
					 clause,subject,subject.dterm);}
			else {
			    var role=this.KNode(clause.slice(1,pstart));
			    var object=this.KNode(clause.slice(pstart+1,pend));
			    object.add(role.dterm,subject);
			    subject.add('genls',role);}}
		    else subject.add('genls',this.KNode(clause.slice(1)));}
		break;
	    case '_': {
		var object=this.KNode(clause.slice(1));
		subject.add('examples',object);
		object.add('genls',subject);
		break;}
	    case '-':
		subject.add('never',this.KNode(clause.slice(1)));
		break;
	    case '&': {
		var value=clause.slice((clause[1]==="-") ? (2) : (1));
		var assoc=this.KNode(value);
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
		    subject.add('equiv',this.KNode(clause.slice(2)));
		else if (clause[1]==='~')
		    subject.add('kinda',this.KNode(clause.slice(2)));
		else 
		    subject.add('identical',this.KNode(clause.slice(1)));
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
		var mirror=this.KNode(clause.slice(1));
		if (subject.mirror===mirror) break;
		else {
		    var omirror=subject.mirror;
		    fdjtLog.warn("Inconsistent mirrors for %s: +%s and -%s",
				 subject,mirror,omirror);
		    omirror.mirror=false;}
		if (mirror.mirror) {
		    var oinvmirror=mirror.mirror;
		    fdjtLog.warn("Inconsistent mirrors for %s: +%s and -%s",
				 mirror,subject,oinvmirror);
		    omirror.mirror=false;}
		subject.mirror=mirror; mirror.mirror=subject;
		break;}
	    case '.': {
		var brk=findBreak(clause,'=');
		if (!(brk))
		    throw {name: 'InvalidClause', irritant: clause};
		var role=this.KNode(clause.slice(1,brk));
		var object=this.KNode(clause.slice(brk+1));
		this.add(role.dterm,object);
		object.add('genls',role);
		break;}
	    default: {
		var brk=findBreak(clause,'=');
		if (brk>0) {
		    var role=this.KNode(clause.slice(0,brk));
		    var object=this.KNode(clause.slice(brk+1));
		    subject.add(role.dterm,object);
		    object.add('genls',role);}
		else subject.addTerm(clause);}}
	    return subject;}
	Knodule.prototype.handleClause=handleClause;

	function handleSubjectEntry(entry){
	    var clauses=segmentString(entry,"|");
	    var subject=this.KNode(clauses[0]);
	    if (this.trace_parsing>2)
		fdjtLog("[%fs] Processing subject entry %s %o %o",
			fdjtET(),entry,subject,clauses);
	    var i=1; while (i<clauses.length)
		this.handleClause(clauses[i++],subject);
	    if (this.trace_parsing>2)
		fdjtLog("[%fs] Processed subject entry %o",fdjtET(),subject);
	    return subject;}
	Knodule.prototype.handleSubjectEntry=handleSubjectEntry;

	function handleEntry(entry){
	    entry=trimspace(entry);
	    if (entry.length===0) return false;
	    var bar=fdjtString.findSplit(entry,'|');
	    var atsign=fdjtString.findSplit(entry,'@');
	    if ((atsign>0) && ((bar<0)||(atsign<bar))) {
		var term=entry.slice(0,atsign);
		var knostring=((bar<0) ? (entry.slice(atsign+1)) :
			       (entry.slice(atsign+1,bar)));
		var knodule=Knodule(knostring);
		if (bar<0) return knodule.KNode(term);
		else return knodule.handleEntry(term+entry.slice(bar));}
	    switch (entry[0]) {
	    case '*': {
		var subject=this.handleSubjectEntry(entry.slice(1));
		if (!(fdjtKB.contains(this.key_concepts,subject)))
		    this.key_concepts.push(subject);
		return subject;}
	    case '-': {
		var subentries=segmentString(entry.slice(1),"/");
		var knowdes=[];
		var i=0; while (i<subentries.length) {
		    knowdes[i]=this.KNode(subentries[i]); i++;}
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
	Knodule.prototype.handleEntry=handleEntry;

	function handleEntries(block){
	    if (typeof block === "string") {
		var nocomment=stripComments(block);
		var segmented=segmentString(nocomment,';');
		if (this.trace_parsing>1)
		    fdjtLog("[%fs] Handling %d entries",fdjtET(),segmented.length);
		return this.handleEntries(segmented);}
	    else if (block instanceof Array) {
		var results=[];
		var i=0; while (i<block.length) {
		    results[i]=this.handleEntry(block[i]); i++;}
		return results;}
	    else throw {name: 'TypeError', irritant: block};}
	Knodule.prototype.handleEntries=handleEntries;

	Knodule.prototype.def=handleSubjectEntry;

	Knodule.def=function(string,kno){
	    if (!(kno)) kno=Knodule.knodule;
	    return kno.def(string);};

	Knodule.prototype.trace_parsing=0;

	return Knodule;})();

var KNode=Knodule.KNode;

function KnoduleIndex(knodule) {
    if (knodule) this.knodule=knodule;
    this.byweight={}; this.bykey={}; this.tagweights={}; this._alltags=[];
    return this;}

KnoduleIndex.prototype.add=function(item,key,weight,kno)
{
    if (key instanceof KNode) {
	if ((key.knodule)===(this.knodule))
	    key=key.dterm;
	else key=key.tagString();}
    if (typeof weight !== 'number')
	if (weight) weight=2; else weight=0;
    if ((weight)&&(!(this.byweight[weight])))
	this.byweight[weight]={};
    if (this.bykey[key]) fdjtKB.add(this.bykey[key],item);
    else {
	this.bykey[key]=fdjtKB.Set(item);
	this._alltags.push(key);}
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
KnoduleIndex.prototype.freq=function(key){
    if (this.bykey[key])
	return this.bykey[key].length;
    else return 0;};
KnoduleIndex.prototype.find=function(key){
    if (this.bykey[key]) return this.bykey[key];
    else return [];};
KnoduleIndex.prototype.score=function(key,scores){
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
KnoduleIndex.prototype.tagScores=function(){
    if (this._tagscores) return this._tagscores;
    var tagscores={}; var tagfreqs={}; var alltags=[];
    var book_tags=this._all;
    var byweight=this.byweight;
    for (var w in byweight) {
	var tagtable=byweight[w];
	for (var tag in tagtable) {
	    var howmany=tagtable[tag].length;
	    if (tagscores[tag]) {
		tagscores[tag]=tagscores[tag]+w*howmany;
		tagfreqs[tag]=tagfreqs[tag]+howmany;}
	    else {
		tagscores[tag]=w*howmany;
		tagfreqs[tag]=howmany;
		alltags.push(tag);}}}
    tagfreqs._count=alltags.length;
    alltags.sort(function (x,y) {
	var xlen=tagfreqs[x]; var ylen=tagfreqs[y];
	if (xlen==ylen) return 0;
	else if (xlen>ylen) return -1;
	else return 1;});
    tagscores._all=alltags; tagscores._freq=tagfreqs;
    this._tagscores=tagscores;
    return tagscores;};


/* Emacs local variables
;;;  Local variables: ***
;;;  compile-command: "cd ..; make" ***
;;;  End: ***
*/
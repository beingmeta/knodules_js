/* -*- Mode: Javascript; Character-encoding: utf-8; -*- */

/* Copyright (C) 2009-2012 beingmeta, inc.
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
	    knodule.prime=[]; knodule.primescores={};
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
	    // DRULES (disambiguation rules)
	    knodule.drules={};
	    return knodule;}
	Knodule.prototype=new fdjtKB.Pool();

	function KNode(knodule,string,lang){
	    if (!(knodule)) return this;
	    var weak=false; var prime=
		((string[0]==='*')&&(string.search(/[^*]/)));
	    var newprime=false;
	    if (string[0]==='~') {weak=true; string=string.slice(1);}
	    else if (prime) {
		string=string.slice(prime);
		if (!(knodule.primescores[string])) {
		    if (prime>(knodule.primescores[string]))
			knodule.primescores[string]=prime;
		    newprime=true;}}
	    if (string.search(/[a-zA-Z]\$/)===0) {
		lang=string.slice(0,2).toUpperCase();
		string=string.slice(3);}
	    else if (lang) lang=lang.toUpperCase();
	    else lang=knodule.language;
	    var term=string;
	    if (knodule.language!==lang) term=lang+"$"+string;
	    if (knodule.dterms.hasOwnProperty(term))
		return knodule.dterms[term];
	    /* Try taking this out, knodule name is implicit
	       in structure */
	    /*
	    var dterm=((this instanceof KNode)?
		       (knodule.ref(string+"@"+knodule.name,this)):
		       (knodule.ref(string+"@"+knodule.name)));
	    */
	    var dterm=((this instanceof KNode)?
		       (knodule.ref(string,this)):
		       (knodule.ref(string)));
	    dterm.dterm=term;
	    if (weak) dterm.weak=true;
	    if (prime) dterm.prime=prime;
	    if ((prime)&&(newprime)) knodule.prime.push(dterm);
	    knodule.dterms[dterm._id]=dterm;
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
	    if (string instanceof KNode) {
		if (string.pool===this)
		    // Should this do some kind of import?
		    return string;
		else return string;}
	    else return new KNode(this,string,lang);};
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
	KNode.prototype.newtagString=function(kno) {
	    return this.dterm;}; /* return this.dterm+"@"+this.knodule.name; */
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
		fdjtLog("Handling clause '%s' for %o",clause,subject);
	    switch (clause[0]) {
	    case '^':
		if (clause[1]==='~') 
		    subject.add('sometimes',this.KNode(clause.slice(2)));
		else if (clause[2]==='*') 
		    subject.add('commonly',this.KNode(clause.slice(2)));
		else {
		    var pstart=findBreak(clause,"(");
		    if (pstart>0) {
			var pend=findBreak(clause,")",pstart);
			if (pend<0) {
			    fdjtLog.warn(
				"Invalid Knodule clause '%s' for %o (%s)",
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
		fdjtLog("Processing subject entry %s %o %o",
			entry,subject,clauses);
	    var i=1; while (i<clauses.length)
		this.handleClause(clauses[i++],subject);
	    if (this.trace_parsing>2)
		fdjtLog("Processed subject entry %o",subject);
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
		var score=entry.search(/[^*]/);
		var trimmed=entry.slice(score);
		var subject=this.handleSubjectEntry(trimmed);
		var prime=this.prime; var scores=this.primescores;
		if (scores[subject._id])
		    scores[subject._id]=scores[subject._id]+score;
		else {
		    prime.push(subject);
		    scores[subject._id]=score;}
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
		    fdjtLog("Handling %d entries",segmented.length);
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


var KnoduleIndex=(function(){
    var isobject=fdjtKB.isobject;
    var objectkey=fdjtKB.objectkey;
    
    function KnoduleIndex(knodule) {
	if (knodule) this.knodule=knodule;
	this.items={}; this.tags={}; this._alltags=[]; this._allitems=[];
	this._ranked=false; this.ranks=false;
	this.tagscores={}; this.tagfreqs={}; this.maxscore=0; this.maxfreq=0;
	return this;}
    
    KnoduleIndex.prototype.add=function(item,tag,weight,kno){
	var itemkey=((typeof item === 'object')?(objectkey(item)):(item));
	if ((typeof tag === 'string')&&(kno)) tag=kno.ref(tag)||tag;
	var tagkey=(((typeof tag === 'string')&&(tag))||
		    ((tag.tagString)&&(tag.tagString()))||
		    ((tag instanceof KNode)&&(tag.dterm))||
		    (objectkey(tag)));
	var items=this.items, tags=this.tags;
	var alltags=this._alltags, allitems=this._allitems;
	var tagfreqs=this.tagfreqs;
	var tagscores=this.tagscores;
	var itemv=false, iscores=false;
	if ((weight)&&(typeof weight !== 'number')) weight=1;
	if (items.hasOwnProperty(tagkey)) {
	    itemv=items[tagkey];
	    fdjtKB.add(itemv,itemkey);
	    var freq=tagfreqs[tagkey]+1;
	    if (freq>this.maxfreq) this.maxfreq=freq;
	    tagfreqs[tagkey]=freq;}
	else {
	    items[tagkey]=itemv=[itemkey];
	    tagfreqs[tagkey]=1;
	    if (this.maxfreq===0) this.maxfreq=1;
	    alltags.push(tagkey);
	    if (tag!==tagkey) alltags[tagkey]=tag;}
	if (itemv.hasOwnProperty('_scores')) iscores=itemv._scores;
	if ((weight)&&(!(iscores))) itemv._scores=iscores={};
	if (tags.hasOwnProperty(itemkey))
	    fdjtKB.add(tags[itemkey],tagkey);
	else {
	    tags[itemkey]=tagv=[tagkey];
	    allitems.push(itemkey);}
	if (weight) {
	    if (tagv[tagkey]) tagv[tagkey]=+weight;
	    else tagv[tagkey]=weight;
	    var tagscore=(tagscores[tagkey]||0)+weight;
	    tagscores[tagkey]=tagscore;
	    if (tagscore>this.maxscore) this.maxscore=tagscore;
	    if (itemv[itemkey]) itemv[itemkey]=+weight;
	    else itemv[itemkey]=+weight;}
	if ((tag)&&(tag._always)) {
	    var always=tag._always;
	    var i=0; var len=always.length;
	    while (i<len)
		this.add(itemkey,always[i++].dterm,((weight)&&(weight>i)&&(weight-i)));}
	// Invalidate ranks.  In the future, this might do something more incremental
	this.ranks=false;};

    KnoduleIndex.prototype.freq=function(tag){
	if (this.items.hasOwnProperty(tag))
	    return this.items[tag].length;
	else return 0;};
    KnoduleIndex.prototype.find=function(tag){
	if (this.items.hasOwnProperty(tag)) return this.items[tag];
	else return [];};
    
    KnoduleIndex.prototype.rankTags=function(){
	if (this.ranks) return this.ranks;
	else {
	    var ranked=[].concat(this._alltags);
	    var ranks={};
	    var tagscores=this.tagscores, tagfreqs=this.tagfreqs;
	    ranked.sort(function(tag1,tag2){
		var tscore1=tagscores[tag1], tscore2=tagscores[tag2];
		if ((tscore1)&&(tscore2)) {
		    if (tscore1>tscore2) return -1;
		    else if (tscore1<tscore2) return 1;}
		else if (tscore1) return -1;
		else if (tscore2) return 1;
		/* Nothing based on tagscores */
		var freq1=tagfreqs[tag1], freq2=tagfreqs[tag2];
		if (freq1>freq2) return -1;
		else if (freq2>freq1) return 1;
		else return 0;});
	    var i=0; var lim=ranked.length;
	    while (i<lim) {ranks[ranked[i]]=i; i++;}
	    this._ranked=ranked;
	    this.ranks=ranks;
	    return ranks;}};

    // This takes an array of tags (with possible .scores)
    //  and combines them into an array with unique elements
    //  and combined scores
    function combineTags(tagsets,weights){
	var tags=[]; var scores={};
	var tagscores=[];
	var i=0; var lim=tagsets.length;
	while (i<lim) {
	    if ((tagsets[i])&&(tagsets[i].scores))
		tagscores.push(tagsets[i].scores);
	    i++;}
	var i=0; var lim=tagsets.length;
	while (i<lim) {
	    var taglist=tagsets[i++];
	    if (!(taglist)) continue;
	    var j=0; var jlim=taglist.length;
	    while (j<jlim) {
		var tag=taglist[j]; var score=0;
		if (!(scores[tag])) {
		    tags.push(tag);
		    var k=0; var klim=tagscores.length;
		    while (k<klim) {
			var tscore=tagscores[k++][tag];
			if (tscore) score=score+tscore;}}
		scores[tag]=(((weights)&&(weights[i]))||1)+score;
		j++;}}
	tags.scores=tagscores;
	return tags;}
    KnoduleIndex.combineTags=combineTags;
    KnoduleIndex.prototype.combineTags=combineTags;
    Knodule.combineTags=combineTags;

    return KnoduleIndex;})();


/* Emacs local variables
   ;;;  Local variables: ***
   ;;;  compile-command: "cd ..; make" ***
   ;;;  End: ***
*/

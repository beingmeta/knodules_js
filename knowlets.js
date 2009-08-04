/* -*- Mode: Javascript; -*- */

/* Copyright (C) 2009 beingmeta, inc.
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

/* A few global variables.  Maybe we should make these fields on Knowlet. */
var knowlets={};
var knowlet_nicknames={};
var knowlet_langs={};
var protoknowlet={};
var protoknowde={};
var knowlet=false;
var knowlets_debug_parsing=false;
var knowlets_debug_edits=false;

/* Knowlets, constructor, etc. */

function KnowletType(id,lang) {
  var knowlet=this;
  // The name of the knowlet
  knowlet.name=id;
  knowlets[id]=knowlet;
  // Whether the knowlet is indexed (e.g. keeps inverse indices for
  // relations and rules)
  knowlet.indexed=true;
  // Whether to validate asserted relations
  knowlet.validate=true;
  // Whether the knowlet is 'strict' in requiring dterm references for
  // values
  knowlet.strict=false;
  // Whether the knowlet is 'finished' (all references declared)
  knowlet.finished=false;
  // Terms which are assumed unique.  This is used in non-strict
  // knowlets to catch terms that become ambiguous.
  knowlet.unique_terms=[];
  // The default language for this knowlet
  knowlet.language=(((lang) && (knowlet_langs[lang])) || (lang) || "EN");
  // Mapping dterms to Knowdes (unique)
  knowlet.dterms={};
  // A vector of all dterms local to this knowlet
  knowlet.alldterms=[];
  // Mapping external dterms to knowdes
  knowlet.xdterms={};
  // A vector of all foreign references
  knowlet.allxdterms=[];
  // Mapping terms to arrays of of Knowdes (ambiguous)
  knowlet.terms={};
  // Mapping hook terms to arrays of of Knowdes (ambiguous)
  knowlet.hooks={};
  // Inverted indices
  knowlet.genlsIndex={};
  knowlet.index={};
  knowlet.roleIndex={};
  // Key concepts
  knowlet.key_concepts=[];
  // DRULES (disambiguation rules)
  knowlet.drules={};
  // It's own version of Knowde
  knowlet.Knowde= function (dterm,strict) {
    return Knowde(dterm,knowlet,(strict)||knowlet.strict);};
  return knowlet;
}
protoknowlet=KnowletType.prototype;

function Knowlet(id,lang)
{
  var knowlet=knowlets[id];
  if (knowlet) return knowlet;
  else knowlet=knowlet_nicknames[id];
  if (knowlet) return knowlet;
  // We'll ignore this, since Knowlet is often not called with 'new'
  else return new KnowletType(id,lang);
}

protoknowlet.KnowdeProbe= function (string,langid) {
  var langterm=false;
  if ((langid) && (langid!==this.language))
    string="$"+langid+"$"+string;
  if (this.dterms.hasOwnProperty(string))
    return this.dterms[string];
  else if (this.strict) return false;
  else if ((this.terms.hasOwnProperty(string)) &&
	   (this.terms[string].length===1))
    return this.terms[string][0];
  else return false;
};
protoknowlet.KnowdeRef= function(string,langid) {
  var knowde=this.KnowdeProbe(string,((langid)||false));
  if (knowde) return knowde;
  if (this.finished)
    throw {name: 'unknown Knowde reference', irritant: string };
 else return this.Knowde(string,false);
};

/* Text processing utilities */

protoknowlet.stdspace=function(string)
{
  return string.replace(/\s+/," ").
    replace(/^\s/,"").replace(/\s$/,"");
};

protoknowlet.trimspace=function(string)
{
  return string.replace(/^\s/,"").replace(/\s$/,"");
};

protoknowlet.findBreak=function(string,brk,start)
{
  var pos=string.indexOf(brk,start||0);
  while (pos>0)
    if (string[pos-1]!="\\")
      return pos;
    else pos=string.indexOf(brk,pos+1);
  return pos;
};

var _knowlet_oddpat=/(\\)|(\s\s)|(\s;)|(\s;)/g;

protoknowlet.segmentString=function(string,brk,start,keepspace)
{
  if (start)
    if (string.slice(start).search(_knowlet_oddpat)<0)
      return string.slice(start).split(brk);
    else {}
  else if (string.search(_knowlet_oddpat)<0)
    return string.split(brk);
  else {}
  var result=[]; var i=0, pos=start||0;
  var nextpos=this.findBreak(string,brk,pos);
  while (nextpos>=0) {
    var item=((keepspace) ? (string.slice(pos,nextpos)) :
	      (this.stdspace(string.slice(pos,nextpos))));
    if ((item) && (item !== "")) result.push(item);
    pos=nextpos+1;
    nextpos=this.findBreak(string,brk,pos);}
  result.push(string.slice(pos));
  return result;
};


protoknowlet.stripComments=function(string)
{
  return string.replace(/^\s*#.*$/g,"").
    replace(/^\s*\/\/.*$/g,"");
};

/* Knowdes */

function KnowdeType(dterm,knowlet,strict)
{
  var knowde=this;
  if (knowlets_debug_parsing)
    fdjtLog('Making knowde from %s in %o',dterm,knowlet);
  knowde.dterm=dterm; knowde.dangling=true;
  knowlet.dterms[dterm]=knowde;
  knowlet.alldterms.push(dterm);
  knowde.knowlet=knowlet;
  // These are words which can refer (normatively or peculiarly) to this concept
  knowde.terms=new Array(dterm); knowde.hooks=[];
  // These are various relationships
  knowde.roles={}
  knowde.allGenls=[];
  return knowde;
}
protoknowde=KnowdeType.prototype;

function Knowde(dterm,kno,strict)
{
  if (!(kno))
    if (knowlet) kno=knowlet;
    else throw { name: "no default knowlet" };
  if (kno.dterms.hasOwnProperty(dterm))
    return kno.dterms[dterm];
  else if ((!(strict)) && (!(knowlet.strict)) &&
	   (knowlet.terms[dterm]) &&
	   (knowlet.terms[dterm].length===1))
    return knowlet.terms[dterm][0];
  else return new KnowdeType(dterm,kno);
}

/* Knowde semantic relationships (getting) */

protoknowde.getRel=function(rel,infer) {
  if (infer) {}
  else if (this[rel])
    return this[rel];
  else return [];
};
protoknowde.testRel=function(rel,val,infer) {
  if (infer) {}
  else if (this[rel])
    if (this[rel].indexOf(val)<0)
      return false;
    else return true;
  else return false;
};
protoknowde.addRel=function(rel,val) {
  if ((this[rel]) && (this[rel].indexOf(val)>=0))
    return this;
  else {
    var values; var mirror=false;
    var knowlet=this.knowlet;
    var index=knowlet.index;
    if (rel==='never') mirror='never';
    if (this.hasOwnProperty(rel))
      values=this[rel];
    else this[rel]=values=[];
    values.push(val);
    if (mirror)
      if (!(val[mirror]))
	val[mirror]=new Array(this);
      else val[mirror].push(this);
    else {}
    if ((rel==='genls') && (this.allGenls.indexOf(val)<0)) {
      // Keep allgenls updated
      var genls=this.genls; var allgenls=[].concat(genls); 
      var i=0; while (i<genls.length) 
		 allgenls=allgenls.concat(genls[i++].allGenls);
      this.allGenls=allgenls;
      // Update genlsIndex if indexing
      if (index) {
	var allindex=knowlet.genlsIndex;
	var j=0; while (j<allgenls.length) {
	  var g=allgenls[j++];
	  if ((g) && (g.dterm)) {
	    var gdterm=g.dterm;
	    if (allindex.hasOwnProperty(gdterm)) {
	      if (allindex[gdterm].indexOf(this)<0) 
		allindex[gdterm].push(this);}
	    else allindex[gdterm]=new Array(this);}
	  else fdjtWarn("Odd genl %g from allgenls %o of %o",
			g,allgenls,this);}}}
    if (index) {
      fdjtAdd(index,rel,val);
      if (mirror) fdjtAdd(index,val.dterm,mirror,this);}};}

protoknowde.addRole=function(role,val) {
  var rterm=role.dterm;
  if ((this.roles.hasOwnProperty(rterm)) &&
      (this.roles[rterm].indexOf(val)>=0))
    return this;
  else {
    var values=((this.roles.hasOwnProperty(rterm)) && (this.roles[rterm]));
    var knowlet=this.knowlet;
    var index=knowlet.rolesIndex;
    if (values) values.push(val);
    else this.roles[rterm]=values=new Array(val);
    if (index) 
      fdjtIndexAdd(index,this.dterm,rterm,val);}
};

/* Adding synonyms and hooks */

protoknowde.addTerm=function (term,langid) {
  var knowlet=this.knowlet;
  if ((langid) && (langid!==knowlet.language))
    term="$"+langid+"$"+term;
  else {}
  this.dangling=false;
  if (this.terms.indexOf(term)>=0) return;
  this.terms.push(term);
  fdjtAdd(knowlet.terms,term,this);
  return this;};

protoknowde.addHook=function (term,langid) {
  var knowlet=this.knowlet;
  if ((langid) && (langid!==knowlet.language))
    term="$"+langid+"$"+term;
  else {}
  this.dangling=false;
  fdjtAdd(this,"hooks",term);
  fdjtAdd(knowlet.hooks,term,this);
  return this;};

/* DRULEs */

protoknowde.drule={};
protoknowde.drule.prototype=Array;
protoknowlet.parseDRuleElt=
  function (elt,literal) {
  if (elt==="")
    throw { name: 'InvalidDRule', irritant: arguments};
  else if (literal) return elt;
  else if (elt[0]==="'") return elt.slice(1);
  else if (elt[0]==="\"")
    if (elt[-1]==="\"")
      return elt.slice(1,-1);
    else return elt.slice(1);
  else if (elt[0]===":")
    return this.Knowde(elt.slice(1));
  else if (this.dterms[elt]) return this.dterms[elt];
  else return elt;
}
  
protoknowlet.KnowDRule=
  function(head) {
  var drule=new Array();
  var i=0; while (i<arguments.length) {
    var arg=arguments[i++];
    if (typeof arg === "string")
      drule.push(this.parseDRuleElt(arg));
    else if (arg instanceof Array) {
      var j=0; while (j<arg.length)
		 drule.push(this.parseDRuleElt(arg[j++]));}
    else throw { name: "InvalidDRule", irritant: arguments};}
  drule.head=drule[0];
  return drule;};

/* Processing the PLAINTEXT microformat */

protoknowlet.handleClause=function(clause,subject) {
  if (knowlets_debug_parsing)
    fdjtLog("Handling clause '%s' for %o",clause,subject);
  switch (clause[0]) {
  case '^':
    if (clause[1]==='~') 
      subject.addRel('sometimes',this.KnowdeRef(clause.slice(2)));
    else if (clause[2]==='*') 
      subject.addRel('commonly',this.KnowdeRef(clause.slice(2)));
    else {
      var pstart=this.findBreak("(");
      if (pstart>0) {
	var pend=this.findBreak(")",pstart);
	if (pend<0) {
	  fdjtWarn("Invalid Knowlet clause '%s' for %o (%s)",
		   clause,subject,subject.dterm);}
	else {
	  var role=this.KnowdeRef(clause.slice(1,pstart));
	  var arg=this.KnowdeRef(clause.slice(pstart+1,pend));
	  arg.addRole(role,subject);
	  subject.addRel('genls',role);}}
      else subject.addRel('genls',this.KnowdeRef(clause.slice(1)));}
    break;
  case '_': {
    var object=this.KnowdeRef(clause.slice(1));
    subject.addRel('examples',object);
    object.addRel('genls',subject);
    break;}
  case '-':
    subject.addRel('never',this.KnowdeRef(clause.slice(1)));
    break;
  case '~':
    if (clause.search(/~[A-Za-z][A-Za-z]\$/)===0)
      subject.addHook(clause.slice(4),clause.slice(1,3).toLowerCase());
    else subject.addHook(clause.slice(1));
    break;
  case '&': {
    var value=clause.slice((clause[1]==="-") ? (2) : (1));
    var assoc=this.KnowdeRef(value);
    if (clause[1]==="-")
      subject.addRel('antiassocs',assoc);
    else subject.addRel('assocs',assoc);
    break;}
  case '@': 
    if (clause[1]==="#") 
      fdjtAdd(subject,'tags',clause.slice(2));
    else fdjtAdd(subject,'uri',clause.slice(1));
    break;
  case '=':
    if (clause[1]==='@')
      subject.oid=clause.slice(1);
    else if (clause.indexOf('@')>1) {
      var atpos=clause.indexOf('@');
      var knowlet=Knowlet(clause.slice(atpos+1));
      var knowde=this.Knowde(clause.slice(1,atpos));
      var mirror_name=subject.dterm+"@"+subject.knowlet.name;
      knowlet.xdterms[mirror_name]=subject;
      knowlet.allxdterms.push(subject);
      if (subject.xdterms) subject.xdterms.push(clause.slice(1));
      else subject.xdterms=new Array(clause.slice(1));
      subject.knowlet.xdterms[clause.slice(1)]=knowde;
      subject.knowlet.allxdterms.push(clause.slice(1));}
    else if (clause[1]==='*')
      subject.addRel('equiv',this.KnowdeRef(clause.slice(2)));
    else if (clause[1]==='~')
      subject.addRel('kinda',this.KnowdeRef(clause.slice(2)));
    else 
      subject.addRel('identical',this.KnowdeRef(clause.slice(2)));
    break;
  case '"': {
    var qend=((clause[-1]==='"') ? (-2) : (-1));
    if (clause[1]==="*") {
      fdjtAdd(subject,"glosses",clause.slice(2,qend));
      subject.gloss=clause.slice(2);}
    else if (!(subject.gloss)) {
      fdjtAdd(subject,"glosses",clause.slice(1,qend));
      subject.gloss=clause.slice(1,qend);}
    else fdjtAdd(subject,"glosses",clause.slice(2,qend));
    break;}
  case '%': {
    var mirror=KnowdeRef(clause.slice(1));
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
    var brk=this.findBreak(clause,'=');
    if (!(brk))
      throw {name: 'InvalidClause', irritant: clause};
    var role=this.KnowdeRef(clause.slice(1,brk));
    var filler=this.KnowdeRef(clause.slice(brk+1));
    this.addRole(role,filler);
    break;}
  default: {
    var brk=this.findBreak(clause,'=');
    if (brk>0) {
      var role=this.KnowdeRef(clause.slice(0,brk));
      var filler=this.KnowdeRef(clause.slice(brk+1));
      subject.addRole(role,filler);
      filler.addRel('genls',role);}
    else if ((brk=this.findBreak(clause,'\&'))>0) {
      var drule=this.KnowDRule(this.segmentString(clause,'&'));
      drule.knowde=subject;
      if (subject.drules)
	subject.drules.push(drule);
      else subject.drules=new Array(drule);
      if (subject.knowlet.drules.hasOwnProperty(drule.head))
	subject.knowlet.drules[drule.head].push(drule);
      else subject.knowlet.drules[drule.head]=new Array(drule);}
    else if (clause.search(/[A-Za-z][A-Za-z]\$/)===0) {
      subject.addTerm(clause.slice(3),clause.slice(0,3).toLowerCase());}
    else subject.addTerm(clause);}}
  return subject;
};

protoknowlet.handleSubjectEntry=function(entry)
{
  var clauses=this.segmentString(entry,"|");
  var subject=this.Knowde(clauses[0]);
  if (knowlets_debug_parsing)
    fdjtLog("Processing subject entry %s %o %o",entry,subject,clauses);
  var i=1; while (i<clauses.length)
	     this.handleClause(clauses[i++],subject);
  if (knowlets_debug_parsing)
    fdjtLog("Processed subject entry %o",subject);
  return subject;
};

protoknowlet.handleEntry=function(entry)
{
  entry=this.trimspace(entry);
  if (entry.length===0) return false;
  var bar=fdjtFindSplit(entry,'|');
  var atsign=fdjtFindSplit(entry,'@');
  if ((atsign>0) && ((bar<0)||(atsign<bar))) {
    var term=entry.slice(0,atsign);
    var knostring=((bar<0) ? (entry.slice(atsign+1)) :
		   (entry.slice(atsign+1,bar)));
    var knowlet=Knowlet(knostring);
    if (bar<0) return knowlet.Knowde(term);
    else return knowlet.handleEntry(term+entry.slice(bar));}
  switch (entry[0]) {
  case '*': {
    var subject=this.handleSubjectEntry(entry.slice(1));
    if (this.key_concepts.indexOf(subject)<0)
      this.key_concepts.push(subject);
    return subject;}
  case '-': {
    var subentries=this.segmentString(entry.slice(1),"/");
    var knowdes=[];
    var i=0; while (i<subentries.length) {
      knowdes[i]=KnowdeRef(subentries[i]); i++;}
    var j=0; while (j<knowdes.length) {
      var k=0; while (k<knowdes.length) {
	if (j!=k) knowdes[j].addDisjoin(knowdes[k]);
	k++;}
      j++;}
    return knowdes[0];}
  case '/': {
    var pos=1; var subject=false; var head=false;
    var next=this.findBreak(entry,'/',pos);
    while (true) {
      var basic_level=false;
      if (entry[pos]==='*') {basic_level=true; pos++;}
      var next_subject=
	((next) ? (this.handleSubjectEntry(entry.slice(pos,next))) :
	 (this.handleSubjectEntry(entry.slice(pos))));
      if (subject) subject.addGenl(next_subject);
      else head=next_subject;
      subject=next_subject;
      if (basic_level) subject.basic=true;
      if (next) {
	pos=next+1; next=this.findBreak(entry,"/",pos);}
      else break;}
    return head;}
  default:
    return this.handleSubjectEntry(entry);
  }
};

protoknowlet.handleEntries=function(block)
{
  if (typeof block === "string") {
    var nocomment=this.stripComments(block);
    var segmented=this.segmentString(nocomment,';');
    if (knowlets_debug_parsing)
      fdjtLog("Handling %d entries",segmented.length);
    return this.handleEntries(segmented);}
  else if (block instanceof Array) {
    var results=[];
    var i=0; while (i<block.length) {
      results[i]=this.handleEntry(block[i]); i++;}
    return results;}
  else throw {name: 'TypeError', irritant: block};
};

/* KnowDef returns a knowde from an entry */

function KnowDef(string,kno)
{
  if ((typeof string !== "string") || (string.length<1))
    throw {name: 'TypeError', irritant: string};
  var termstart=-1; var oid=false; var result=false;
  if ((string[0]==="@") && ((termstart=string.indexOf("\""))>0)) {
    oid=string.slice(0,termstart);
    string=string.slice(termstart+1,string.length-1);}
  if ((oid) && (oid.startsWith("@1/"))) 
    result=brico_knowlet.handleSubjectEntry(oid+"|"+string);
  else {
    // Get the head and (possibly) the knowlet
    var bar=string.search(/[^\\]\|/g);
    var head=((bar<0) ? (string) : (string.slice(0,bar)));
    var atsign=head.search(/[^\\]@/g);
    var dterm;
    if (atsign>0) {
      kno=Knowlet(head.slice(atsign+1));
      dterm=head.slice(0,atsign);
      result=kno.handleSubjectEntry(dterm+string.slice(bar));}
    else {
      if (!(kno)) kno=knowlet; dterm=head;
      result=kno.handleSubjectEntry(string);}}
  if ((oid) && (result) && (typeof result != "string"))
    result.oid=oid;
  return result;
}

/* Getting tag strings */

function knoTagString(knowde,knowlet)
{
  if (typeof knowde === "string")
    return knowde;
  else if (knowde.oid)
    return knowde.oid+"\""+knowde.dterm+"\"";
  else if (knowlet)
    if (knowlet===knowde.knowlet)
      return knowde.dterm;
    else return knowde.dterm+"@"+knowde.knowlet.name;
  else return knowde.dterm;
}

/* Indexing with knowlets */

var kno_wgenls=false;
var kno_wogenls=true;

function knoIndexTag(index,tag,indexval,nogenls,checkdup)
{
  var dup=false;
  var dterm=((typeof tag === "string") ? (tag) : (tag.dterm));
  if (index.hasOwnProperty(dterm))
    if (!(checkdup))
      index[dterm].push(indexval);
    else if (index[dterm].indexof(indexval)<0)
      index[dterm].push(indexval);
    else dup=true;
  else {
    if (index._all) index._all.push(dterm);
    index[dterm]=new Array(indexval);}
  if (dup) return false;
  else if ((nogenls) || (typeof tag==="string")) return true;
  else {
    // Assume it's a Knowde
    var genls=tag.allGenls;
    if (genls) {
      var i=0; while (i<genls.length) {
	var g=genls[i++]; var gdterm=g.dterm;
	if (index.hasOwnProperty(gdterm))
	  index[gdterm].push(indexval);
	else {
	  if (index._all) index._all.push(gdterm);
	  index[gdterm]=new Array(indexval);}}}
    return true;}
}

var brico_knowlet=Knowlet("brico","en");

/* Emacs local variables
;;;  Local variables: ***
;;;  compile-command: "cd ..; make" ***
;;;  End: ***
*/

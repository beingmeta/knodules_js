/* A few global variables.  Maybe we should make these fields on Knowlet. */

var knowlets={};
var knowlet_nicknames={};
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
  knowlet.alwaysIndex={};
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
  if (this.dterms[string]) return this.dterms[string];
  else if (langid) {
    langterm="$"+langid+"$"+string;
    if (this.dterms[langterm])
      return this.dterms[langterm];}
  if (this.strict) return false;
  else if ((this.terms[string]) &&
	   (this.terms[string].length===1))
    return this.terms[string][0];
  else if ((langterm) &&
	   (this.terms[langterm]) &&
	   (this.terms[langterm].length===1))
    return this.terms[langterm][0];
  else return false;
};
protoknowlet.KnowdeRef= function(string,langid) {
  var knowde=this.KnowdeProbe(string,((langid)||(this.language)));
  if (knowde) return knowde;
  if (this.finished)
    throw {name: 'unknown Knowde reference', irritant: string };
 else return this.Knowde(string,false);
};

/* Text processing utilities */

protoknowlet.quote_char="\\";

protoknowlet.stdspace=function(string)
{
  return string.replace(/\s+/," ").
    replace(/^\s/,"").replace(/\s$/,"");
};

protoknowlet.findBreak=function(string,brk,start)
{
  var pos=string.indexOf(brk,start||0);
  while (pos>0)
    if (string[pos-1]!=this.quote_char)
      return pos;
    else pos=string.indexOf(brk,pos+1);
  return pos;
};

protoknowlet.segmentString=function(string,brk,start,keepspace)
{
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
  return knowde;
}
protoknowde=KnowdeType.prototype;

function Knowde(dterm,kno,strict)
{
  if (!(kno))
    if (knowlet) kno=knowlet;
    else throw { name: "no default knowlet" };
  var knowde=kno.dterms[dterm];
  if (knowde) return knowde;
  else if ((!(strict)) && (!(knowlet.strict)) &&
	   (knowlet.terms[dterm]) &&
	   (knowlet.terms[dterm].length===1))
    return knowlet.terms[dterm][0];
  else return new KnowdeType(dterm,kno,strict);
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
    var values=this[rel]; var mirror=false;
    var knowlet=this.knowlet;
    var index=knowlet.index;
    if (rel==='never') mirror='never';
    if (values) values.push(val);
    else this[rel]=values=new Array(val);
    if (mirror)
      if (!(val[mirror]))
	val[mirror]=new Array(this);
      else val[mirror].push(this);
    else {}
    if (index) {
      fdjtAdd(index,rel,val);
      if (mirror) fdjtAdd(index,val.dterm,mirror,this);
      if (rel==='always') {
	var allindex=knowlet.alwaysIndex;
	function indexAlways(g) {
	  var gdterm=g.dterm;
	  if (knowlet.alwaysIndex[gdterm])
	    if (knowlet.alwaysIndex[gdterm].indexOf(g)>=0)
	      return;
	    else knowlet.alwaysIndex[gdterm].push(g);
	  else knowlet.alwaysIndex[gdterm]=new Array(g);
	  if (g.always) {
	    var always=g.always; var i=0;
	    while (i<always.length) indexAlways(always[i++]);}}
	indexAlways(val);}}}
};

protoknowde.addRole=function(role,val) {
  var rterm=role.dterm;
  if ((this.roles[rterm]) && (this.roles[rterm].indexOf(val)>=0))
    return this;
  else {
    var values=this.roles[rterm];
    var mirror=(role.mirror)|false;
    var knowlet=this.knowlet;
    var index=knowlet.rolesIndex;
    var mterm=((mirror) && (mirror.dterm));
    if (values) values.push(val);
    else this.roles[rterm]=values=new Array(val);
    if (index) {
      fdjtAdd(index,rterm,val);
      if (mirror) fdjtAdd(index,val.dterm,mterm,this);}}
};

/* Adding synonyms and hooks */

protoknowde.addTerm=function (term,langid) {
  var knowlet=this.knowlet;
  if (langid)
    if (langid===knowlet.language)
      if (term.search("$"+knowlet.language+"$",4)===0)
	term=term.slice(4);
      else {}
    else if (term.search("$"+langid+"$",4)===0) {}
    else term="$"+langid+"$";
  else {}
  this.dangling=false;
  if (this.terms.indexOf(term)>=0) return;
  this.terms.push(term);
  fdjtAdd(knowlet.terms,term,this);
  return this;};

protoknowde.addHook=function (term,langid) {
  var knowlet=this.knowlet;
  if (langid)
    if (langid===knowlet.language)
      if (term.search("$"+knowlet.language+"$",4)===0)
	term=term.slice(4);
      else {}
    else if (term.search("$"+langid+"$",4)===0) {}
    else term="$"+langid+"$";
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
	  subject.addRel('always',role);}}
      else subject.addRel('always',clause.slice(1));}
    break;
  case '_': {
    var object=this.KnowdeRef(clause.slice(1));
    this.addRel('examples',object);
    object.addRel('always',subject);
    break;}
  case '-':
    subject.addRel('never',clause.slice(1));
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
    else subject.addRel('assocs',assoc);}
  case '@': 
    if (clause[1]==="#") 
      fdjtAdd(subject,'tags',clause.slice(2));
    else fdjtAdd(subject,'uri',clause.slice(1));
  case '=':
    if (clause[1]==='@')
      subject.oid=clause.slice(1);
    else if (clause.indexOf('@')>1) {
      var atpos=clause.indexOf('@');
      var knowlet=Knowlet(clause.slice(atpos+1));
      var knowde=knowlet.Knowde(clause.slice(1,atpos));
      var mirror_name=subject.dterm+"@"+subject.knowlet.name;
      knowlet.xdterms[mirror_name]=subject;
      knowlet.allxdterms.push(subject);
      if (subject.xdterms) subject.xdterms.push(clause.slice(1));
      else subject.xdterms=new Array(clause.slice(1));
      subject.knowlet.xdterms[clause.slice(1)]=knowde;
      subject.knowlet.allxdterms.push(clause.slice(1));}
    else if (clause[1]==='*')
      this.addRel('equiv',knowlet.KnowdeRef(clause.slice(2)));
    else if (clause[1]==='~')
      this.addRel('kinda',knowlet.KnowdeRef(clause.slice(2)));
    else 
      this.addRel('identical',knowlet.KnowdeRef(clause.slice(2)));
    break;
  case '"': {
    var qend=((clause[-1]==='"') ? (-2) : (-1));
    if (clause[1]==="*") {
      fdjtAdd(subject,"gloss",clause.slice(2,qend));
      subject.gloss=clause.slice(2);}
    else if (subject.gloss)
      fdjtAdd(subject,"gloss",clause.slice(2,qend));
    else {
      fdjtAdd(subject,"gloss",clause.slice(1,qend));
      subject.gloss=clause.slice(1,qend);}
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
    subject.mirror=mirror; mirror.mirror=subject;}
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
      filler.addRel('always',role);}
    else if ((brk=this.findBreak(clause,'\&'))>0) {
      var drule=this.KnowDRule(this.segmentString(clause,'&'));
      drule.knowde=subject;
      if (subject.drules)
	subject.drules.push(drule);
      else subject.drules=new Array(drule);
      if (subject.knowlet.drules[drule.head])
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
    return this.handleEntries(segmented);}
  else if (block instanceof Array) {
    var results=[];
    var i=0; while (i<block.length) {
      results[i]=this.handleEntry(block[i]); i++;}
    return results;}
  else throw {name: 'TypeError', irritant: block};
};

/* Getting knowdes into HTML */

protoknowde.toHTML=function()
{
  if (this.dterm_base)
    return fdjtSpan("dterm",this.dterm_base,
		    fdjtSpan("disambig",this.dterm_disambig));
  else {
    var dterm=this.dterm;
    var colonpos=dterm.indexOf(':');
    if ((colonpos>0) && (colonpos<(dterm.length-1))) {
      if (dterm[colonpos+1].search(/\w/)===0)
	return fdjtSpan("dterm",dterm.slice(0,colonpos),
			dterm.slice(colonpos));}
    return fdjtSpan("dterm",dterm);}
}

/* Getting Knowlets out of HTML */

var _knowletHTMLSetup_done=false;

function knowletHTMLSetup(node)
{
  var doing_the_whole_thing=false;
  if ((!(node)) || (node_arg===document))
    if (_knowletHTMLSetup_done) return;
    else {
      if (!(node)) {
	node=document;
	doing_the_whole_thing=true;}
      else if (node===document)
	doing_the_whole_thing=true;}
  var elts=fdjtGetChildrenByTagName(document,"META");
  var i=0; while (i<elts.length) {
    var elt=elts[i++];
    if (elt.name==="KNOWLET") {
      knowlet=Knowlet(elt.content);}}
  if ((!(knowlet)) &&
      (document) && (document.location) &&
      (document.location.href)) {
    var url=document.location.href;
    var hash=url.indexOf("#");
    if (hash>=0) url=url.slice(0,hash);
    fdjtLog("Using '%s' as the name of the default knowlet",url);
    knowlet=Knowlet(url);}
  i=0; while (i<elts.length) {
    var elt=elts[i++];
    if (elt.name==="KNOWDEF") knowlet.handleEntry(elt.content);}
  elts=fdjtGetChildrenByTagName(document,"LINK");
  i=0; while (i<elts.length) {
    var elt=elts[i++];
    if (elt.name==="KNOWLET") {
      knowlet.handleEntry(elt.content);}}
  elts=fdjtGetChildrenByTagName(document,"SCRIPT");
  i=0; while (i<elts.length) {
    var elt=elts[i++];
    if ((elt.getAttribute("language")) &&
	((elt.getAttribute("language"))==="knowlets")) {
      var children=elt.childNodes;
      var j=0; while (i<children.length) {
	var child=children[j++];
	if (child.nodeType===Node.TEXT_NODE)
	  knowlet.handleEntries(child.nodeValue);}}}
  if (doing_the_whole_thing) _knowletHTMLSetup_done=true;
}



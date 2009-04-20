var knowlets_table={};
var knowlet_nicknames={};
var knowlet_prototype={};
var knowde_prototype={};

function Knowlet(id,lang) {
  var knowlet=knowlets_table[id];
  if (knowlet) return knowlet;
  else knowlet=knowlet_nicknames[id];
  if (knowlet) return knowlet;
  // We'll ignore this, since Knowlet is often not called with 'new'
  else knowlet={};
  // The name of the knowlet
  knowlet.name=id;
  knowlets_table[id]=knowlet;
  // The prototype (which is the same as Knowlet.prototype)
  knowlet.prototype=knowlet_prototype;
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
  // Terms which are assumed unique
  knowlet.unique_terms=[];
  // The default language for this knowlet
  knowlet.lang=(((lang) && (knowlet_langs[lang])) || (lang) || "EN");
  // Mapping dterms to Knowdes (unique)
  knowlet.dterms={};
  // Mapping terms to arrays of of Knowdes (ambiguous)
  knowlet.terms={};
  // Mapping hook terms to arrays of of Knowdes (ambiguous)
  knowlet.hooks={};
  // Mapping langids to term tables
  knowlet.xterms={};
  // Mapping langids to hook tables
  knowlet.xhooks={};
  // Inverted index of GENLS and GENLS*
  knowlet.byGenls={};
  knowlet.byByAllGenls={};
  // Inverted index of antonyms, including expansion over GENLS*
  knowlet.byAntonyms={};
  knowlet.byByAllAntonyms={};
  // Maps roles to inverted indices of fillers, indicates whether a role exists
  knowlet.byRole={}; knowlet.hasRoles={};
  // Key concepts
  knowlet.key_concepts=[];
  // DRULES (disambiguation rules)
  knowlet.drules={};
  // It's own version of Knowde
  knowlet.Knowde(dterm,strict) {
    return Knowde(dterm,knowlet,(strict)||knowlet.strict);}
  return knowlet;
}
knowlet_prototype=Knowlet.prototype;
knowlet_prototype.KnowdeProbe(string,langid) {
  if (this.dterms[string]) return this.dterms[string];
  else if (this.strict) return false;
  else if ((!(langid)) || (langid===this.language))
    if ((this.terms[string]) && (this.terms[string].length===1))
      return this.terms[string][0];
    else return false;
  else if (this.xterms[langid])
    if ((this.xterms[langid][string]) &&
	(this.xterms[langid][string].length===1))
      return this.xterms[langid][string][0];
    else return false;
  else return false;
}
knowlet_prototype.KnowdeRef(string,langid) {
  var knowde=KnowdeProbe(string,((langid)||(this.language)));
  if (knowde) return knowde;
  if (this.finished)
    throw {exception: 'unknown reference', irritant: string };
 else return this.Knowde(string,false);
}

function Knowde(dterm,knowlet,strict)
{
  var knowde=knowlet.dterms[dterm];
  if (knowde) return knowde;
  else if ((!(strict)) && (!(knowlet.strict)) &&
	   (knowlet.terms[dterm]) &&
	   (knowlet.terms[dterm].length===1))
    return knowlet.terms[dterm][0];
  // We'll ignore this, since Knowde is often not called with 'new'
  else knowde={};
  knowde.prototype=knowde_prototype;
  knowde.dterm=dterm;
  knowde.dangling=true;
  knowde.terms=[]; knowde.hooks=[];
  // This maps langids to arrays of terms or hooks
  knwode.xterms={}; knowde.xhooks={};
  knowde.genls=[]; knowde.specls=[];
  knowde.roles={}; knowde.assocs=[];
  knowde.disjoins=[];
  return knowde;
}
knowde_prototype=Knowde.prototype;

/* Knowde semantic relationships (getting) */

knowde_prototype.getGenls() {
  var results=[];
  function helper(g) {
    if (results.indexOf(g)) return;
    results.push(g);
    var genls=g.genls;
    var i=0; while (i<genls.length) helper(genls[i++]);}
  var genls=this.genls;
  while (i<genls.length) helper(genls[i++]);
  return results;}
knowde_prototype.getDisjoins() {
  var results=[];
  function helper(g) {
    if (results.indexOf(g)) return;
    results.push(g);
    var genls=g.genls;
    var i=0; while (i<genls.length) helper(genls[i++]);}
  var disjoins=this.disjoins;
  while (i<disjoins.length) helper(disjoins[i++]);
  return results;}

/* Knowde semantic relationships (testing) */

knowde_prototype.hasGenl(genl) {
  if (genl instanceof String) genl=this.knowlet.KnowdeRef(genl);
  else if (!(genl instanceof Knowde))
    throw {exception: "not a Knowde", irritant: genl;}
  if (this.genls.indexOf(genl)>=0) return true;
  else if (this.knowlet.indexed)
    return ((this.knowlet.byAllGenls[genl]) &&
	    (this.knowlet.byAllGenls[genl].indexOf(this)>=0));
  var visits=[];
  function helper(g) {
    if (g.genls.indexOf(genl)>=0) return true;
    else if (visits.indexOf(g)>=0) return false;
    else {
      visits.push(g);
      var genls=g.genls;
      var i=0; while (i<genls.length)
		 if (helper(genls[i++])) return true; else {}
      return false;}}
  if (this.genls.indexOf(genl)>=0) return true;
  else {
    while (i<genls.length)
      if (helper(genls[i++])) return true; else {}
    return false;}
}

knowde_prototype.disjointFrom(disj) {
  var visits=[];
  if (disj instanceof String) genl=this.knowlet.KnowdeRef(disj);
  else if (!(disj instanceof Knowde))
    throw {exception: "not a Knowde", irritant: genl;}
  if (this.disjoins.indexOf(genl)>=0) return true;
  else if (this.knowlet.indexed)
    return ((this.knowlet.byAllDisjoins[disj]) &&
	    (this.knowlet.byAllDisjoins[disj].indexOf(this)>=0));
  function helper(g) {
    if (g.disjoins.indexOf(genl)>=0) return true;
    else if (visits.indexOf(g)>=0) return false;
    else {
      visits.push(g);
      var genls=g.genls;
      var i=0; while (i<genls.length)
		 if (helper(genls[i++])) return true;
		 else {}
      return false;}}
  while (i<genls.length)
    if (helper(genls[i++])) return true; else {}
  return false;
}

/* Knowde semantic relationships (adding) */

knowde_prototype.addGenl=function (genl) {
  if (genl instanceof String) genl=this.knowlet.KnowdeRef(genl);
  else if (!(genl instanceof Knowde))
    throw {exception: "not a Knowde", irritant: genl;}
  if (this.genls.indexOf(genl)) return this;
  else {
    this.dangling=false; this.genls.push(genl); genl.specls.push(this);
    if (knowlet.indexed) {
      var knowde=this, knowlet=this.knowlet;
      function indexAllGenls(g) {
	var gdterm=g.dterm;
	if (knowlet.byAllGenls[gdterm])
	  if (knowlet.byAllGenls[gdterm].indexOf(knowde)>=0)
	    return;
	  else knowlet.byAllGenls[gdterm].push(knowde);
	else knowlet.byAllGenls[gdterm]=new Array(knowde);
	var genls=g.genls; var i=0;
	while (i<genls.length) indexAllGenls(genls[i++]);}
      if (knowlet.byGenls[gdterm])
	knowlet.byGenls[gdterm].push(this);
      else knowlet.byGenls[gdterm]=new Array(this);
      if (knowlet.byGenls[gdterm])
	knowlet.byGenls[gdterm].push(this);
      else knowlet.byGenls[gdterm]=new Array(this);
      indexAllGenls(genl);}
    return knowde;}
};
knowde_prototype.addDisjoin=function (disj) {
  if (disj instanceof String) disj=this.knowlet.KnowdeRef(disj);
  else if (!(disj instanceof Knowde))
    throw {exception: "not a Knowde", irritant: disj;}
  if (this.disjoins.indexOf(disj)) return this;
  else {
    this.dangling=false; this.disjoins.push(disj); disj.disjoins.push(this);
    if (this.knowlet.indexed) {
      var knowde=this, knowlet=this.knowlet, disjdterm=disj.dterm;
      function indexAllDisjoins(g) {
	var gdterm=g.dterm;
	if (knowlet.byAllDisjoins[gdterm])
	  if (knowlet.byAllDisjoins[gdterm].indexOf(knowde)>=0)
	    return;
	  else knowlet.byAllDisjoins[gdterm].push(knowde);
	else knowlet.byAllDisjoins[gdterm]=new Array(knowde);
	var genls=g.genls; var i=0;
	while (i<genls.length) indexAllDisjoins(genls[i++]);}
      if (knowlet.byDisjoins[disjdterm])
	knowlet.byGenls[disjdterm].push(this);
      else knowlet.byDisjoins[disjdterm]=new Array(this);
      if (knowlet.byDisjoins[disjdterm])
	knowlet.byDisjoins[disjdterm].push(this);
      else knowlet.byDisjoins[disjdterm]=new Array(this);
      indexAllDisjoins(disj);}
    return knowde;}
};

knowde_prototype.addAssoc=function (assoc) {
  if (assoc instanceof String) assoc=this.knowlet.KnowdeRef(assoc);
  else if (!(assoc instanceof Knowde))
    throw {exception: "not a Knowde", irritant: disj;}
  if (this.assocs.indexOf(assoc)) return this;
  else {
    this.assocs.push(assoc);
    return this;}
};

/* Asserting rules */

knowde_prototype.addRole=function (role,filler) {
  if (role instanceof String) role=this.knowlet.KnowdeRef(role);
  else if (!(role instanceof Knowde))
    throw {exception: "not a Knowde", irritant: role;}
  if (filler instanceof String) filler=this.knowlet.KnowdeRef(role);
  else if (!(filler instanceof Knowde))
    throw {exception: "not a Knowde", irritant: filler;}
  this.dangling=false;
  var rdterm=role.dterm;
  if (this.roles[rdterm])
    if (this.roles.indexOf(filler)<0)
      this.roles[rdterm].push(filler);
    else return;
  else this.roles[rdterm]=new Array(filler);
  if (role.mirror) {
    var mdterm=role.mirror.dterm;
    if (filler.roles[mdterm])
      filler.roles[mdterm].push(this);
    else filler.roles[mdterm]=new Array(this);}
  if (this.knowlet.indexed) {
    this.indexRole(role,filler);
    if (role.mirror) filler.indexRole(role.mirror,this);}
}
knowde_prototype.indexRole=function(role,filler) {
  var rdterm=role.dterm;
  var fdterm=filler.dterm;
  var knowlet=this.knowlet;
  if (knowlet.hasRoles[rdterm])
    if (knowlet.hasRoles[rdterm].indexOf(this)<0)
      knowlet.hasRoles[rdterm].push(this); else {}
  else knowlet.hasRoles[rdterm]=new Array(this);
  var role_index;
  if (knowlet.byRoles[rdterm])
    role_index=knowlet.byRoles[rdterm];
  else knowlet.byRoles[rdterm]=role_index={};
  if (role_index[fdterm])
    role_index[fdterm].push(this);
  else role_index[fdterm]=new Array(this);
}

/* Adding synonyms and hooks */

knowde_prototype.addTerm=function (term,langid) {
  if (langid) langid=knowlet_langids[langid]||langid;
  else if (this.terms.indexOf(term)) return;
  this.dangling=false;
  if ((!(langid)) || (langid===this.knowlet.language)) {
    this.terms.push(term);
    if (this.knowlet.terms[term])
      this.knowlet.terms[term].push(this);
    else this.knowlet.terms[term]=new Array(this);}
  else {
    var terms=this.xterms[langid];
    if (!(terms)) {
      this.xterms[langid]=terms={};
      terms[term]=new Array(this);}
    else if (terms[term]) terms[term].push(this);
    else terms[term]=new Array(this);}
  return this;};

knowde_prototype.addHook=function (term,langid) {
  if (langid) langid=knowlet_langids[langid]||langid;
  else if (this.hooks.indexOf(term)) return;
  this.dangling=false;
  if ((!(langid)) || (langid===this.knowlet.language)) {
    this.hooks.push(term);
    if (this.knowlet.hooks[term])
      this.knowlet.hooks[term].push(this);
    else this.knowlet.hooks[term]=new Array(this);}
  else {
    var terms=this.xhooks[langid];
    if (!(terms)) {
      this.xhooks[langid]=terms={};
      terms[term]=new Array(this);}
    else if (terms[term]) terms[term].push(this);
    else terms[term]=new Array(this);}
  return this;};

/* Processing the PLAINTEXT microformat */

knowlet_prototype.handleClause(clause,subject) {
  switch (clause[0]) {
  case '^':
    subject.addGenl(clause.slice(1)); break;
  case '_':
    this.KnowdeRef(clause.slice(1)).addGenl(subject); break;
  case '-':
    subject.addDisjoin(clause.slice(1));
  case '~':
    if (false)
      subject.addHook(clause.slice(4));
    else subject.addHook(clause.slice(1));
    break;
  case 's':
    break;
  default:
    if (false)
      subject.addHook(clause.slice(3));
    subject.addTerm(clause);}
  return subject;
}

knowlet_prototype.handleSubjectEntry(entry)
{
  var clauses=entry.slice('|');
  var subject=this.Knowde(clauses[0]);
  var i=1; while (i<clauses.length)
	     this.handleClause(clauses[i++],subject);
  return subject;
}

knowlet_prototype.handleEntry(entry)
{
  switch (entry[0]) {
  case '*': {
    var subject=this.handleSubjectEntry(entry.slice(1));
    if (this.key_concepts.indexOf(subject)<0)
      this.key_concepts.push(subject);
    return subject;}
  default:
    return this.handleSubjectEntry(entry);
  }
}

knowlet_prototype.handleEntries(entry)
{
  if (entry instanceof Array) {
    var results=[];
    var i=0; while (i<entry.length) {
      results[i]=this.handleEntry(entry[i]); i++;}
    return results;}
  else if (entry instanceof String)
    return this.handleEntries(entry.split(';'));
  else throw {exception: 'type error', irritant: entry};
}

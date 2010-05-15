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

KnowletIndex.Query=
  (function(){
    function Query(index,query) {
      if (!(index)) return this;
      if (!(this instanceof Query)) return new Query(this,index);
      if (typeof query === "string") query=this.string2query(query);
      var qstring=this.query2string(query);
      var cached=((index.cache)&&(index.cache[qstring]));
      if (cached) return cached;
      // Construct the results object
      this.index=index; this._query=query; this._qstring=qstring;
      this._results=[]; this._scores={};
      if (query.length===0) {
	this._refiners={_results: index._alltags};
	return this;}
      this._start=new Date();
      // Do the search
      this.do_search();
      this._done=new Date();
      if (this._refiners) {}
      else if (this._results.length>1)
	this._refiners=this.get_refiners();
      else this._refiners={_results: []};
      this._refined=new Date();
      if (this.index.trace)
	fdjtLog("In %f secs, %o yielded %d results: %o",
		((this._done.getTime()-this._start.getTime())/1000),
		query,result._results.length,result._results);
      if (this.index.trace)
	fdjtLog("In %f secs, query %o yielded %d refiners: %o",
		((this._refined.getTime()-this._done.getTime())/1000),
		query,result._refiners._results.length,
		result._refiners._results);
      if (index.cache) index.cache[qstring]=this;
      return this;}
    Knowlet.Query=Query;
    KnowletIndex.Query=Query;
    KnowletIndex.prototype.Query=function(string){
      return new Query(this,string);}

    function string2query(string) {
      if (typeof string === "string") {
	var lastsemi=string.lastIndexOf(';');
	if (lastsemi>0)
	  return string.slice(0,lastsemi).split(';');
	else return [];}
      else return string;}
    Query.string2query=string2query;
    Query.prototype.string2query=string2query;

    function query2string(query){
      if (!(query)) query=this.query;
      if ((typeof query === "object") && (query instanceof Array))
	if (query.length===0) return "";
	else return query.join(';')+';';
      else return query;}
    Query.prototype.cache={};
    Query.prototype.query2string=query2string;
    Query.query2string=query2string;

    Query.base=function(string) {
      var lastsemi=string.lastIndexOf(';');
      if (lastsemi>0)
	return string.slice(0,lastsemi+1);
      else return "";};
    Query.tail=function(string) {
      var lastsemi=string.lastIndexOf(';');
      if (lastsemi>0)
	return string.slice(lastsemi+1);
      else return string;};

    function do_search(results) {
      if (!(results)) results=this;
      var query=results._query; var scores=results._scores;
      var base=false;
      // A query is an array of terms.  In a simple query,
      // the results are simply all elements which are tagged
      // with all of the query terms.  In a linear scored query,
      // a score is based on how many of the query terms are matched,
      // possibly with weights based on the basis of the match.
      var i=0; while (i<query.length) {
	var term=query[i++];
	var items=results.index.find(term);
	if (results.index.trace)
	  fdjtLog("Query element '%s' matches %d items",term,items.length);
	if (items.length===0) continue;
	else if (base)
	  base=fdjtKB.intersection(base,items);
	else base=items;}
      var allitems=base;
      results._results=allitems;
      i=0; var n_items=allitems.length;
      while (i<n_items) {
	var item=allitems[i++];
	var tags=results.index.Tags(item);
	var j=0; var lim=query.length; var cur;
	while (j<lim) {
	  var tag=query[j++];
	  if (cur=scores[item])
	    scores[item]=cur+tags[item]||1;
	  else scores[item]=tags[item]||1;}}
      // Initialize scores for all of results
      return results;}
    Query.do_search=do_search;
    Query.prototype.do_search=function() { return do_search(this);};

    function get_refiners(results) {
      if (!(results)) results=this;
      // This gets terms which can refine this search, particularly
      // terms which occur in most of the results.
      if (results._refiners) return results._refiners;
      var query=results._query;
      var rvec=(results._results);
      var refiners={};
      var scores=(results._scores)||false; var freqs={};
      var alltags=[];
      var i=0; while (i<rvec.length) {
	var item=rvec[i++];
	var item_score=((scores)&&(scores[item]));
	var tags=results.index.Tags(item)||[];
	if (tags) {
	  var j=0; var len=tags.length; while (j<len) {
	    var tag=tags[j++];
	    // If the tag is already part of the query, we ignore it.
	    if (fdjtKB.contains(query,tag)) {}
	    // If the tag has already been seen, we increase its frequency
	    // and its general score
	    else if (freqs[tag]) {
	      freqs[tag]=freqs[tag]+1;
	      if (item_score) refiners[tag]=refiners[tag]+item_score;}
	    else {
	      // If the tag hasn't been counted, we initialize its frequency
	      // and score, adding it to the list of all the tags we've found
	      alltags.push(tag); freqs[tag]=1;
	      if (item_score) refiners[tag]=item_score;}}}}
      freqs._count=rvec.length;
      refiners._freqs=freqs;
      results._refiners=refiners;
      alltags.sort(function(x,y) {
	  if (freqs[x]>freqs[y]) return -1;
	  else if (freqs[x]===freqs[y]) return 0;
	  else return 1;});
      refiners._results=alltags;
      if ((results.index.trace)&&(results.index.trace>1))
	fdjtLog("Refiners for %o are (%o) %o",
		results._query,refiners,alltags);
      return refiners;}
    Query.get_refiners=get_refiners;
    Query.prototype.get_refiners=function() {return get_refiners(this);};

    return Query;
  })();


/* Emacs local variables
;;;  Local variables: ***
;;;  compile-command: "cd ..; make" ***
;;;  End: ***
*/

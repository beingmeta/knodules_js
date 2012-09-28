/* -*- Mode: Javascript; Character-encoding: utf-8; -*- */

/* ##################### knodules/query.js ####################### */

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

KnoduleIndex.Query=
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
	    this._results=[]; this._scores={}; this._counts={};
	    if (query.length===0) {
		this._refiners={_results: index._alltags};
		return this;}
	    this._start=new Date();
	    // Do the search
	    this.do_search();
	    this._done=new Date();
	    if (this._refiners) {}
	    else this._refiners=this.get_refiners();
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
	Knodule.Query=Query;
	KnoduleIndex.Query=Query;
	KnoduleIndex.prototype.Query=function(query){
	    return new Query(this,query);}

	// Queries are sets of terms and interchangable between vectors
	// and strings with semi-separated tag names

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
	    if ((typeof query === "object") && (query instanceof Array)) {
		if (query.length===0) return "";
		else {
		    var i=0, lim=query.length; var result="";
		    while (i<lim) {
			if (i>0) result=result+";";
			var elt=query[i++], id=false;
			if (typeof elt === 'string')
			    result=result+elt;
			else if (id=((elt._qid)||(elt.oid)||
				     (elt.uuid)||(elt._id)))
			    result=result+id;
			else result=result+elt;}
		    return result;}}
	    else return query;}
	Query.prototype.cache={};
	Query.prototype.query2string=query2string;
	Query.prototype.getString=query2string;
	Query.query2string=query2string;

	function do_search(results) {
	    if (!(results)) results=this;
	    var query=results._query;
	    var scores=results._scores; var counts=results._counts;
	    var matches=[];
	    var allitems=false;
	    // A query is an array of terms.  In a simple query,
	    // the results are simply all elements which are tagged
	    // with all of the query terms.  In a linear scored query,
	    // a score is based on how many of the query terms are matched,
	    // possibly with weights based on the basis of the match.
	    var i=0; while (i<query.length) {
		var term=query[i];
		if (typeof term !== 'string')
		    term=(((term.tagString)&&(term.tagString()))||
			  term._id||term.dterm);
		var items=matches[i]=results.index.find(term);
		var j=0; var jlim=items.length;
		while (j<jlim) {
		    var item=items[j++];
		    // if (scores[item]) scores[item]++; else scores[item]=1;
		    if (counts[item]) counts[item]++; else counts[item]=1;}
		if (results.index.trace)
		    fdjtLog("Query element '%s' matches %d items",
			    term,items.length);
		i++;}
	    if (query.length===1) allitems=matches[0];
	    else {
		// When there are multiple query terms, an item is in
		// the result if it contains at least two of the query
		// terms, with the score being determined by various
		// factors.
		var i=0; var lim=query.length;
		while (i<lim) {
		    var j=0; while (j<lim) {
			if (j>=i) {j++; continue}
			else if (matches[j].length===0) {j++; continue;}
			else if (allitems) {
			    var join=fdjtKB.intersection(matches[i],matches[j]);
			    allitems=fdjtKB.union(allitems,join);}
			else allitems=fdjtKB.intersection(matches[i],matches[j]);
			j++;}
		    i++;}}
	    // Now we apply the tagscores where they're assigned
	    results._results=allitems;
	    var seen_tags={};
	    i=0; var n_items=allitems.length;
	    while (i<n_items) {
		var item=allitems[i++];
		var tags=results.index.tags[item];
		var tagscores=tags.scores;
		var j=0; var lim=query.length; var score=0;
		if (tagscores) {
		    while (j<lim) {
			var tag=query[j++];
			if (!(seen_tags[tag])) seen_tags=true;
			if (tagscores[tag])
			    score=score+(tagscores[tag]*2);
			else score++;}}
		scores[item]=score;}
	    return results;}
	Query.do_search=do_search;
	Query.prototype.do_search=function() { return do_search(this);};

	function get_refiners(results) {
	    if (!(results)) results=this;
	    // This gets terms which can refine this search, particularly
	    // terms which occur in most of the results.
	    if (results._refiners) return results._refiners;
	    var query=results._query;
	    var qterms=[];
	    var rvec=(results._results);
	    var refiners={};
	    var scores=(results._scores)||false; var freqs={};
	    var max_score=0, max_freq=0;
	    var alltags=[];
	    var i=0; while (i<query.length) {
		var q=query[i++];
		qterms.push(q);
		if (q.dterm) qterms.push(q.dterm);
		if (q.dterms) {
		    var dterms=q.dterms; var j=0;
		    while (j<dterms.length) qterms.push(dterms[j++]);}}
	    var i=0, lim=rvec.length; while (i<lim) {
		var item=rvec[i++];
		var item_score=((scores)&&(scores[item]));
		var tags=results.index.tags[item]||[];
		if (typeof tags === 'string') tags=[tags];
		if (tags) {
		    var j=0; var len=tags.length; while (j<len) {
			var tag=tags[j++]; var freq, score;
			// If the tag is already part of the query, we
			// ignore it.
			if (fdjtKB.contains(qterms,tag)) {}
			// If the tag has already been seen, we
			// increase its frequency and its general
			// score
			else if (freq=freqs[tag]) {
			    freq++; freqs[tag]=freq;
			    if (freq>max_freq) max_freq=freq;
			    if (item_score) {
				var score=(refiners[tag]||0)+item_score;
				if (score>max_score) max_score=score;
				refiners[tag]=score;}}
			else {
			    // If the tag hasn't been counted, we
			    // initialize its frequency and score,
			    // adding it to the list of all the tags
			    // we've found
			    alltags.push(tag); freqs[tag]=1;
			    if (max_score<item_score) max_score=item_score;
			    if (item_score) refiners[tag]=item_score;}}}}
	    refiners._count=freqs._count=alltags.length;
	    refiners._freqs=freqs;
	    refiners._maxfreq=max_freq;
	    refiners._maxscore=max_score;
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


/* -*- Mode: Javascript; Character-encoding: utf-8; -*- */

/* ##################### knodules/knodules.js ####################### */

/* Copyright (C) 2009-2013 beingmeta, inc.
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

(function(){

    var RefDB=fdjt.RefDB;
    var Ref=fdjt.Ref;
    var Query=RefDB.Query;
    var KNode=Knodule.KNode;
    var warn=fdjt.Log.warn;

    var tagslot_pats=["%","*%","**%","~%","~~%",
		      "%*","*%*","**%*","~%*","~~%*",
		      "%**","*%**","**%**","~%**","~~%**"];
    var tagslot_weights=
	{"%": 1,"*%": 3,"**%": 5,"~%": 0.5,"~~%": 0.25,
	 "%*": 0.5,"*%*": 1,"**%*": 2,"~%*": 0.25,"~~%*": 0.15,
	 "%**": 0.25,"*%**": 0.5,"**%**": 1,"~%**": 0.15,"~~%**": 0.1};
    
    Knodule.addTags=function addTags(refs,tags,refdb,tagdb,base_slot){
	if (!(base_slot)) base_slot="tags";
	if (typeof tags === "string") tags=[tags];
	else if (tags instanceof Ref) tags=[tags];
	else if (!(tags.length)) tags=[tags];
	else if (tags instanceof Array) {}
	else tags=[].concat(tags);
	if (typeof refs === "string") refs=[refs];
	else if (refs instanceof Ref) refs=[refs];
	else if (refs instanceof Array) {}
	else if (!(refs.length)) refs=[refs];
	else refs=[].concat(refs);
	var slots=new Array(tags.length); var weak=new Array(tags.length);
	var i=0, ntags=tags.length;
	while (i<ntags) {
	    var tag=tags[i]; var slot=base_slot; var weak=false;
	    if (typeof tag === "string") {
		if (tag[0]==="*") {
		    var tagstart=tag.search(/[^*]/);
		    slot=tag.slice(0,tagstart)+base_slot;
		    tag=tag.slice(tagstart);}
		else if (tag[1]==="~") {
		    var tagstart=tag.search(/[^~]/);
		    slot=tag.slice(0,tagstart)+base_slot;
		    tag=tag.slice(tagstart);
		    weak=true;}
		else {}
		if (tagdb) {
		    if ((tag.indexOf('|'))&&
			(tagdb)&&(tagdb.handleSubjectEntry))
			tag=tagdb.handleSubjectEntry(tag);
		    else if (weak) tag=tagdb.probe(tag)||tag;
		    else tag=tagdb.ref(tag)||tag;}}
	    slots[i]=slot; tags[i++]=tag;}
	var j=0, nrefs=refs.length;
	while (j<nrefs) {
	    var refstring=refs[j]; var ref=false;
	    if ((refdb)&&(typeof ref === "string"))
		ref=refdb.ref(refstring);
	    else ref=RefDB.resolve(refstring);
	    if (!(ref)) {
		warn("Couldn't resolve %s to a reference",refstring);
		j++; continue;}
	    refs[j++]=ref;}
	i=0; while (i<ntags) {
	    tag=tags[i], slot=slots[i], weak=(slot[0]=="~");
	    j=0; while (j<nrefs) {
		ref=refs[j++];
		if (!(ref)) continue;
		ref.add(slot,tag);
		if ((tag instanceof Knode)&&(tag.always)) {
		    ref.add(slot+"*",tag.always);
		    ref.add(slot+"**",tag.allways);}}
            i++;}};

    // Knodule.addTags=function addTags(){};

    function TagQuery(tags,dbs,weights,base_slots,base_query){
        if (arguments.length===0) return this;
	var i=0, n_slots, slot, weight, query={};
	if (!(dbs)) dbs=TagQuery.default_dbs||false;
	if (!(base_slots)) {
	    base_slots=["tags"]; n_slots=1;
	    if (!(weights)) weights={tags: 12};}
	else if (typeof base_slots === "string") {
	    base_slots=[base_slots]; n_slots=1;}
	else n_slots=base_slots.length;
	if (!(weights)) weights={};
	if (base_query) {
	    for (var qslot in base_query) {
		if (base_query.hasOwnProperty(qslot)) {
		    query[qslot]=base_query[qslot];}}}
	while (i<n_slots) {
	    slot=base_slots[i++]; weight=weights[slot]||1;
	    var j=0, n_pats=tagslot_pats.length;
	    while (j<n_pats) {
		var pat=tagslot_pats[j++];
		var tagslot=pat.replace("%",slot);
		var dweight=weights[tagslot]||(weight*tagslot_weights[pat]);
		if (!(query[tagslot])) query[tagslot]=tags;
		if (!(weights[tagslot])) weights[tagslot]=dweight;}}
	
	Query.call(this,dbs,query,weights);

	this.base_slots=base_slots;}

    TagQuery.prototype=new Query();
    
    TagQuery.prototype.getTagScores=function getTagScores(results){
	if (this.tagscores) return this.tagscores;
	else if (this.execute()) {
	    if (!(results)) results=this.results;
	    var r=0, n_results=results.length;
	    var scores=this.scores;
	    var tagscores=this.tagscores=(this.tagscores={});
	    var base_slots=this.base_slots;
	    var s=0, n_slots=base_slots.length;
	    while (r<n_results) {
		var result=results[r++];
		s=0; while (i<n_slots) {
		    var slot=base_slots[s++];
		    var ts=0, n_tagslots=tagslot_pats.length;
		    while (ts<n_tagslots) {
			var pat=tagslot_pats[ts++];
			var tagslot=pat.replace("%",slot);
			if (result[tagslot]) {
			    var weight=weights[tagslot];
			    var tags=result[tagslot];
			    var v=0, n_tags=tags.length;
			    while (v<n_tags) {
				var tag=tags[v++];
				if (tagscores[tag]) tagscores[tag]=+weight;
				else tagscores[tag]=weight;}}}}}
	    return tagscores;}
	else return false;};
    
    Knodule.TagQuery=TagQuery;

})();
	 

/* Emacs local variables
   ;;;  Local variables: ***
   ;;;  compile-command: "cd ..; make" ***
   ;;;  indent-tabs-mode: nil ***
   ;;;  End: ***
*/

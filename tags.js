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
    var fdjtMap=fdjt.Map;
    var Query=RefDB.Query;
    var KNode=Knodule.KNode;
    var fdjtLog=fdjt.Log;
    var warn=fdjtLog.warn;

    var fdjtSet=fdjt.Set;

    var getKeyString=RefDB.getKeyString;

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
	var slots=new Array(tags.length);
	var i=0, ntags=tags.length;
	while (i<ntags) {
	    var tag=tags[i]; var slot=base_slot; var weak=false;
	    if (typeof tag === "string") {
		if (tag[0]==="*") {
		    var tagstart=tag.search(/[^*]/);
		    slot=tag.slice(0,tagstart)+base_slot;
		    tag=tag.slice(tagstart);}
		else if (tag[0]==="~") {
		    slot="~"+base_slot;
		    tag=tag.slice(1);
		    weak=true;}
		else {}
                if (tag.indexOf('|')>0) {
                    if (tagdb) tag=tagdb.handleEntry(tag);
                    else if (Knodule.current)
                        tag=Knodule.current.handleEntry(tag);
                    else {}}
                else if ((weak)&&(tagdb))
                    tag=tagdb.probe(tag)||tag;
                else if (weak) {}
                else if (tagdb) tag=tagdb.ref(tag);
                else {}}
	    slots[i]=slot; tags[i]=tag; i++;}
	var j=0, nrefs=refs.length;
	while (j<nrefs) {
	    var refstring=refs[j]; var ref=false;
	    if ((refdb)&&(typeof refstring === "string"))
		ref=refdb.ref(refstring);
	    else ref=RefDB.resolve(refstring,false,Knodule,true);
	    if (!(ref)) {
		warn("Couldn't resolve %s to a reference",refstring);
		j++; continue;}
	    refs[j++]=ref;}
	i=0; while (i<ntags) {
	    tag=tags[i], slot=slots[i];
	    j=0; while (j<nrefs) {
		ref=refs[j++];
		if (!(ref)) continue;
		ref.add(slot,tag);
                if (ref.alltags) ref.alltags.push(tag);
                else ref.alltags=[tag];
                if (tag instanceof Knode) {
                    ref.add('knodes',tag);
                    ref.add(slot+"*",tag);}
		if ((tag instanceof Knode)&&(tag.allways)) 
                    ref.add(slot+"*",tag.allways);}
            i++;}};

    function exportTagSlot(tags,slotid,exported){
        if (!(tags instanceof Array)) tags=[tags];
        var extags=((exported.tags)||(exported.tags=[]));
        var start=slotid.search(/[^*~]+/);
        var end=slotid.search(/[*]*$/);
        var prefix=((start)&&(slotid.slice(0,start)));
        if (end) slotid=slotid.slice(start,end);
        else if (start) slotid=slotid.slice(start);
        var i=0, lim=tags.length; while (i<lim) {
            var tag=tags[i++];
            if (!(tag)) continue;
            var tagstring=((typeof tag === "string")?(tag):(tag._qid||tag.getQID()));
            if (start) extags.push(prefix+tagstring);
            else extags.push(tagstring);}
        return undefined;}
    Knodule.exportTagSlot=exportTagSlot;
            
    function importTagSlot(ref,slotid,tags,data,indexing){
        var keep=[]; var alltags=[];
        var knodule=ref.use_knodule||ref._db.use_knodule||Knodule.current;
        if (!(tags instanceof Array)) tags=[tags];
        var i=0, lim=tags.length; while (i<lim) {
            var tag=tags[i++];
            if (!(tag)) continue;
            else if (tag instanceof Ref) keep.push(tag);
            else if ((typeof tag === "object")&&(tag._id)) {
                var tagref=ref.resolve(tag,knodule,Knodule,true)||tag._id;
                keep.push(tagref);}
            else if (typeof tag === "string") {
                var tag_start=tag.search(/[^*~]/);
                var slot=slotid, tagstring=tag, tagref=false;
                if (tag_start>0) {
                    slot=tag.slice(0,tag_start)+slotid;
                    tagstring=tag.slice(tag_start);}
                var bar=tagstring.indexOf('|');
                if (bar>0) tagterm=tagstring.slice(0,bar);
                else tagterm=tagstring;
                tagref=RefDB.resolve(tagterm,knodule,Knodule,false)||
                    ((knodule)&&(knodule.ref(tagterm)))||
                    tagterm;
                if (bar>0) {
                    if (tagref instanceof Knode) 
                        tagref._db.handleEntry(tagstring);
                    else warn("No knodule for %s",tagstring);}
                alltags.push(tagref);
                if (tagref instanceof KNode) ref.add('knodes',tagref,indexing);
                if (slot!==slotid) ref.add(slot,tagref,indexing);
                else keep.push(tagref);}
            else keep.push(tag);}
        ref["all"+slotid]=fdjtSet(alltags.concat(keep));
        if (keep.length) return keep;
        else return undefined;}
    Knodule.importTagSlot=importTagSlot;

    // Knodule.addTags=function addTags(){};

    var tagslot_pats=["%","*%","**%","~%","%*","*%*","**%*","~%*"];
    var tagslot_weights=
	{"~%": 2,"~%*": 2,"%": 4,"%*": 4,
         "*%": 8, "*%*": 6,"**%": 12, "**%*": 8};

    function TagQuery(tags,dbs,slot_weights){
        if (arguments.length===0) return this;
        var clauses=[], slots=[];
	if (!(dbs)) dbs=TagQuery.default_dbs||false;
        if (!(slot_weights)) slot_weights=this.slots||{"tags": 1};
        if (!(tags instanceof Array)) tags=[tags];
        for (var slot in slot_weights)
            if (slot_weights.hasOwnProperty(slot)) {
                var i_pat=0, n_pats=tagslot_pats.length;
                while (i_pat<n_pats) {
                    var pat=tagslot_pats[i_pat++];
                    var dslot=pat.replace("%",slot);
                    slots.push(dslot);
                    slot_weights[dslot]=
                        (tagslot_weights[pat])*(slot_weights[slot]);}}
        var i_tag=0, n_tags=tags.length;
        while (i_tag<n_tags) {
            clauses.push({fields: slots,values: [tags[i_tag++]]});}
        
        this.tags=tags;
        this.weights=slot_weights;

        return Query.call(this,dbs,clauses,slot_weights);}

    TagQuery.prototype=new Query();
    TagQuery.prototype.execute=function TagQueryExecute(){
        if (this.tags.length===0) {
            var results=[];
            var alldbs=this.dbs;
            var i=0, lim=alldbs.length;
            while (i<lim) results=results.concat(alldbs[i++].allrefs);
            this.results=results;
            return results;}
        else return Query.prototype.execute.call(this);}
    
    var TagMap=window.Map||fdjt.Map;
    var RefMap=fdjt.RefMap;

    TagQuery.prototype.getCoTags=function getCoTags(results){
	if (this.cotags) return this.cotags;
	else if (this.execute()) {
	    if (!(results)) results=this.results;
            var slot_weights=this.weights;
	    var scores=this.scores;
	    var alltags=this.cotags=[];
	    var tagscores=this.tagscores=new TagMap();
	    var tagfreqs=this.tagfreqs=new TagMap();
	    var slots=[], weights=[];
            for (var slot in slot_weights)
                if (slot_weights.hasOwnProperty(slot)) {
                    slots.push(slot); weights.push(slot_weights[slot]);}
            var n_slots=slots.length;
            var max_score=0, max_freq=0;
	    var r=0, n_results=results.length;
	    while (r<n_results) {
		var result=results[r++];
                score=((scores)&&(scores[result._id]))||1;
		var i=0; while (i<n_slots) {
		    var slot=slots[i], weight=weights[i];
                    if (result.hasOwnProperty(slot)) {
			var tags=result[slot];
			var v=0, n_tags=tags.length;
			while (v<n_tags) {
			    var tag=tags[v++]; var tagscore=0, tagfreq=0;
                            var new_freq, new_score;
                            if (!(tagscores.get(tag))) alltags.push(tag);
                            var new_freq=tagfreqs.increment(tag,1);
                            var new_score=tagscores.increment(tag,weight*score);
                            if (new_freq>max_freq) max_freq=new_freq;
                            if (new_score>max_score) max_score=new_score;}}
                    i++;}}
            this.max_tagfreq=max_freq; this.max_tagscore=max_score;
	    return alltags;}
	else return false;};
    TagQuery.prototype.getString=function TagQueryString(){
        var tags=fdjt.Set(this.tags); var qstring="";
        var i=0, lim=tags.length;
        while (i<lim) {
            var tag=tags[i++];
            if (typeof tag === "string")
                qstring=qstring+";"+tag;
            else qstring=qstring+";"+((tag._qid)||(tag.getQID()));}
        return qstring;}
    
    Knodule.TagQuery=TagQuery;

})();
	 

/* Emacs local variables
   ;;;  Local variables: ***
   ;;;  compile-command: "cd ..; make" ***
   ;;;  indent-tabs-mode: nil ***
   ;;;  End: ***
*/

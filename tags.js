/* -*- Mode: Javascript; Character-encoding: utf-8; -*- */

/* ##################### knodules/knodules.js ####################### */

/* Copyright (C) 2009-2015 beingmeta, inc.
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
/* global Knodule: false */

//var fdjt=((window)?((window.fdjt)||(window.fdjt={})):({}));
//var Knodule=window.Knodule;

(function(){
    "use strict";

    var RefDB=fdjt.RefDB;
    var Ref=fdjt.Ref;
    var Query=RefDB.Query;
    var KNode=Knodule.KNode;
    var fdjtLog=fdjt.Log;
    var warn=fdjtLog.warn;

    var fdjtSet=fdjt.Set;

    var slotpat_weights=
        {"~%": 1,"~%*": 1,"%": 4,"%*": 4,"^%": 2,"^%*": 2,
         "*%": 8, "*%*": 6,"**%": 12, "**%*": 8};

    Knodule.addTags=function addTags(refs,tags,refdb,tagdb,base_slot,tagscores){
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
        var i=0, ntags=tags.length, tag, slot, ref;
        while (i<ntags) {
            tag=tags[i]; slot=base_slot; var weak=false;
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
            var refstring=refs[j]; ref=false;
            if ((refdb)&&(typeof refstring === "string"))
                ref=refdb.ref(refstring);
            else ref=RefDB.resolve(refstring,false,Knodule,true);
            if (!(ref)) {
                warn("Couldn't resolve %s to a reference",refstring);
                j++; continue;}
            refs[j++]=ref;}
        i=0; while (i<ntags) {
            tag=tags[i]; slot=slots[i];
            if (tagscores) {
                var slotpat=slot.replace(base_slot,"%");
                var slotweight=slotpat_weights[slotpat];
                if (!(slotweight)) slotweight=3;
                tagscores.increment(tag,nrefs*slotweight);}
            j=0; while (j<nrefs) {
                ref=refs[j++];
                if (!(ref)) continue;
                ref.add(slot,tag,true);
                if (ref.alltags) ref.alltags.push(tag);
                else ref.alltags=[tag];
                if (tag instanceof KNode) {
                    ref.add('knodes',tag);
                    ref.add(slot+"*",tag,true);}
                if ((tag instanceof KNode)&&(tag.allways)) 
                    ref.add(slot+"*",tag.allways,true);}
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
        var keep=[]; var alltags=[], tagref;
        var knodule=ref.tag_knodule||ref._db.tag_knodule||
            Knodule.tag_knodule||Knodule.current;
        if (!(tags instanceof Array)) tags=[tags];
        var i=0, lim=tags.length; while (i<lim) {
            var tag=tags[i++];
            if (!(tag)) continue;
            else if (tag instanceof Ref) keep.push(tag);
            else if ((typeof tag === "object")&&(tag._id)) {
                tagref=ref.resolve(tag,knodule,Knodule,true)||tag._id;
                keep.push(tagref);}
            else if (typeof tag === "string") {
                var tag_start=tag.search(/[^*~]/);
                var tagstring=tag, slot=slotid, tagterm=tag;
                if (tag_start>0) {
                    slot=tag.slice(0,tag_start)+slotid;
                    tagstring=tag.slice(tag_start);}
                var bar=tagstring.indexOf('|');
                if (bar>0) tagterm=tagstring.slice(0,bar);
                else tagterm=tagstring;
                tagref=RefDB.resolve(tagterm,knodule,Knodule,true)||
                    ((knodule)&&(knodule.ref(tagterm)))||
                    tagterm;
                if (bar>0) {
                    if (tagref instanceof KNode) 
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

    function TagQuery(tags,dbs,weights){
        if (arguments.length===0) return this;
        var clauses=[], slots=this.slots=[];
        if (!(dbs)) dbs=TagQuery.default_dbs||false;
        if (!(weights)) weights=this.weights||{"tags": 1};
        if (!(tags instanceof Array)) tags=[tags];
        for (var sl in weights) {
            if (weights.hasOwnProperty(sl)) slots.push(sl);}
        var i_tag=0, n_tags=tags.length;
        while (i_tag<n_tags) {
            var tagval=tags[i_tag++];
            if (typeof tagval === "string")
                clauses.push({fields: 'strings',values: [tagval]});
            else if ((tagval._db)&&(tagval._db.slots)) 
                clauses.push({fields: tagval._db.slots,values: [tagval]});
            else clauses.push({fields: slots,values: [tagval]});}
        
        this.tags=tags;

        return Query.call(this,dbs,clauses,weights);}

    TagQuery.prototype=new Query();
    
    var TagMap=fdjt.Map;
    
    TagQuery.prototype.getCoTags=function getCoTags(results){
        if (this.cotags) return this.cotags;
        else if (this.execute()) {
            if (!(results)) results=this.results;
            var scores=this.scores;
            var slots=this.slots, n_slots=slots.length;
            var alltags=this.cotags=[];
            var tagscores=this.tagscores=new TagMap();
            var tagfreqs=this.tagfreqs=new TagMap();
            var weights=this._weights||this.weights;
            var max_score=0, max_freq=0;
            var r=0, n_results=results.length;
            while (r<n_results) {
                var result=results[r++], seen={};
                var score=((scores)&&(scores[result._id]))||1;
                var s=0; while (s<n_slots) {
                    var slot=slots[s];
                    if (result.hasOwnProperty(slot)) {
                        var tags=result[slot];
                        var weight=weights[slot]||1;
                        if (!(tags)) tags=[];
                        else if (!(tags instanceof Array)) tags=[tags];
                        else {}
                        var v=0, n_tags=tags.length;
                        while (v<n_tags) {
                            var tag=tags[v++];
                            if (!(tagscores.get(tag)))
                                alltags.push(tag);
                            if (!(seen[tag])) {
                                var new_freq=tagfreqs.increment(tag,1);
                                if (new_freq>max_freq) max_freq=new_freq;
                                seen[tag]=true;}
                            var new_score=
                                tagscores.increment(tag,weight*score);
                            if (new_score>max_score)
                                max_score=new_score;}}
                    s++;}}
            this.max_tagfreq=max_freq;
            this.max_tagscore=max_score;
            return alltags;}
        else return false;};
    TagQuery.prototype.getString=function TagQueryString(){
        var tags=fdjt.Set(this.tags); var qstring="";
        var i=0, lim=tags.length;
        while (i<lim) {
            if (i>0) qstring=qstring+";";
            var tag=tags[i++];
            if (typeof tag === "string")
                qstring=qstring+tag;
            else qstring=qstring+((tag._qid)||(tag.getQID()));}
        return qstring;};
    
    Knodule.TagQuery=TagQuery;

})();
         

/* Emacs local variables
   ;;;  Local variables: ***
   ;;;  compile-command: "cd ..; make" ***
   ;;;  indent-tabs-mode: nil ***
   ;;;  End: ***
*/

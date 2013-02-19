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

var Knodule=(function(){
    var fdjtString=fdjt.String;
    var fdjtTime=fdjt.Time;
    var fdjtLog=fdjt.Log;
    var fdjtDOM=fdjt.DOM, fdjtID=fdjt.ID;
    var fdjtUI=fdjt.UI;
    var RefDB=fdjt.RefDB;
    var Ref=fdjt.Ref;
    var warn=fdjtLog.warn;

    var knodules={};
    var all_knodules=[];
    var knodule=false;
    var trace_parsing=0;
    var trace_edits=false;

    var kno_simple_oidpat=/@[0-9A-Fa-f]+\/[0-9A-Fa-f]+/;
    var kno_named_oidpat=/@[0-9A-Fa-f]+\/[0-9A-Fa-f]+(\x22([^\x22]+)\x22)*/;
    var kno_atbreak=/[^\\]@/g;
    
    var lang_pat=/^(([A-Za-z]{2,3}\$)|([A-Za-z]{2,3}_[A-Za-z]{2,3}\$))/;

    function Knodule(id,inits) {
        // Using as a prototype
        if (arguments.length===0) return this;
        if (!(inits)) inits={};
        if (inits.indices)
            inits.indices=inits.indices.concat(
                ["terms","hooks","genls","specls","allgenls"]);
        else inits.indices=["terms","hooks","genls","specls","allgenls"];
        var lang=inits.language;
        var knodule=RefDB.call(this,id,inits);
        if ((lang)&&(knodule.language!==lang))
            throw { error: "language mismatch" };
        // The default language for this knodule
        if ((inits.language)&&(knodule.language)&&
            (inits.language!==knodule.language))
            throw { error: "language mismatch" };
        else if (inits.language)
            knodule.language=inits.language;
        else knodule.language='EN';
        // Mapping dterms (univocal references) to KNode objects
        // (many-to-one).  This redundantly combines refs and altrefs
        // from the underlying ref objects.
        knodule.dterms={};
        // A vector of all dterms local to this knodule
        knodule.alldterms=[];
        // Prime (important) dterms
        knodule.prime=[]; knodule.primescores={};
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
        // Mapping external dterms to their knodes
        knodule.xdterms={};
        // A vector of all foreign knode references
        knodule.allxdterms=[];
        // Inverted index for genls in particular (useful for
        // faster search, inferences, etc)
        knodule.genlsIndex={};
        // This maps external OIDs to knodes
        knodule.oidmap={};
        // DRULES (disambiguation rules)
        knodule.drules={};
        return knodule;}
    Knodule.prototype=new RefDB();

    function KNode(string,knodule,lang){
        if (arguments.length===0) return this;
        var weak=false; var prime=
            ((string[0]==='*')&&(string.search(/[^*]/)));
        var newprime=false, knode=this, notword=false;
        if (string[0]==='~') {weak=true; string=string.slice(1);}
        else if (prime) {
            string=string.slice(prime);
            if (!(knodule.primescores[string])) {
                if (prime>(knodule.primescores[string]))
                    knodule.primescores[string]=prime;
                newprime=true;}}
        var atpos=string.indexOf('@');
        if ((atpos==0)||((atpos===1)&&(string[0]===':'))) notword=true;
        else if ((atpos>2)&&(string[atpos-1]!=='\\')) {
            var domain=string.slice(atpos+1);
            if ((domain!==knodule.name)&&
                (knodule.aliases.indexOf(domain)<0))
                warn("Reference %s is being handled by %s",string,knodule);
            string=string.slice(0,atpos);}
        if (notword) {}
        else if (string.search(lang_pat)===0) {
            var dollar=string.indexOf('$');
            lang=string.slice(0,dollar).toUpperCase();
            string=string.slice(dollar+1);}
        else if (lang) lang=lang.toUpperCase();
        else lang=knodule.language||"EN";
        var refterm=(lang===knodule.language)?(string):lang+"$"+string;
        knode=Ref.call(this,refterm,knodule);
        if (knode===this) {
            knode.dterm=string;
            knode.dterm=refterm;
            knodule.dterms[refterm]=knode;
            knode.allways=fdjt.Set();
            if (lang) knode.add(lang,string);
            knode._live=fdjtTime();}
        if (weak) knode.weak=true;
        if (prime) knode.prime=prime;
        if ((prime)&&(newprime)) knodule.prime.push(knode);
        if ((lang)&&(lang!==knodule.language)) knode.language=lang;
        return knode;}
    KNode.prototype=new RefDB.Ref();
    Knodule.refclass=Knodule.prototype.refclass=KNode;

    Knodule.KNode=KNode;
    Knodule.Knode=KNode;
    Knodule.prototype.KNode=Knodule.prototype.Knode=function(arg,inits) {
        if (arg instanceof KNode) {
            if (arg._db===this)
                // Should this do some kind of import?
                return arg;
            else return arg;}
        else return new KNode(arg,this,inits);};
    Knodule.prototype.cons=function(string,lang) {
        return new KNode(string,this,lang);};
    Knodule.prototype.probe=function(string,langid) {
        if ((this.language===langid)||(!(langid)))
            return this.refs[string]||this.aliases[string]||false;
        else string=langid.toUpperCase()+"$"+string;
        return this.dterms[langid+"$"+string]||false;};
    
    KNode.prototype.add=function(prop,val){
        if ((Ref.prototype.add.call(this,prop,val))&&
            (prop==='genls')) {
            this.allways.push(val);
            this.allways=RefDB.merge(this.allways,val.allways);
            return true;}
        else return false;}
    KNode.prototype.addTerm=function(val,field,inlang){
        if ((typeof val === 'string')&&(val.search(lang_pat)===0)) {
            var dollar=val.indexOf('$');
            var langspec=val.slice(0,dollar).toUpperCase();
            var term=val.slice(dollar+1);
            var lang=this.knodule.language;
            if (langspec===this._db.language) 
                this.add(field,term);
            else this.add(field,langspec+"$"+term);}
        else if (inlang) {
            inlang=inlang.toUpperCase();
            if (inlang===this._db.language)
                this.add(field,val);
            else this.add(field,inlang+"$"+val);}
        else this.add(field,val);};
    KNode.prototype.tagString=function(kno) {
        if (this.oid) return this.oid;
        else if (this.uuid) return this.uuid;
        else if (this._qid) return this._qid;
        if (!(kno)) kno=Knodule.current||false;
        if (kno===this.knodule) return this._id;
        else if (this._db.absrefs) return this._id;
        else if (this._domain)
            return this._id+"@"+this._domain;
        else return this._id+"@"+this._db.name;}
    
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
        if ((clause.length===0)||(clause.search(/[^\n\t ]/g)<0))
            return;
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
        case '+': {
            if (clause[1]==="*") {
                subject.gloss=gloss.slice(2);
                subject.addTerm(subject.gloss,'glosses');}
            else if (clause[1]==="~") {
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
        case '~': {
            var hook=clause.slice(1);
            subject.addTerm(hook,'hooks');
            break;}
        case ':': {
            var equals=findBreak(clause,'=');
            if (equals>0) {
                var field=clause.slice(1,equals);
                var multi=(clause[equals+1]=='+');
                var value=((multi)?(clause.slice(equals+2)):
                           (clause.slice(equals+1)));
                if (multi) subject.add(field,value);
                else subject.store(field,value);}
            subject.add('flags',clause.slice(1));
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
        var weak=false;
        entry=trimspace(entry);
        if (entry.length===0) return false;
        var starpower=entry.search(/[^*]/);
        if (starpower>0) entry=entry.slice(starpower);
        var bar=fdjtString.findSplit(entry,'|');
        var atsign=fdjtString.findSplit(entry,'@');
        var subject;
        if ((atsign>0) && ((bar<0)||(atsign<bar))) {
            // This is a foreign dterm reference (+def), e.g.
            //  dog@beingmeta.com|doggy|^mammal
            var term=entry.slice(0,atsign);
            var knostring=((bar<0) ? (entry.slice(atsign+1)) :
                           (entry.slice(atsign+1,bar)));
            var knodule=Knodule(knostring);
            subject=((bar<0)?(knodule.KNode(term)):
                     (knodule.handleEntry(term+entry.slice(bar))));}
        else subject=this.handleSubjectEntry(entry);
        if (starpower) {
            var id=subject._id;
            var prime=this.prime; var scores=this.primescores;
            var score;
            if (score=scores[id]) {
                if (starpower>score) scores[id]=starpower;}
            else {
                prime.push(id); scores[id]=starpower;}}
        return subject;}
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
var Knode=Knodule.KNode;

/* Emacs local variables
   ;;;  Local variables: ***
   ;;;  compile-command: "cd ..; make" ***
   ;;;  indent-tabs-mode: nil ***
   ;;;  End: ***
*/

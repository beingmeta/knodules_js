/* -*- Mode: Javascript; Character-encoding: utf-8; -*- */

/* ##################### dules/html.js ####################### */

/* Copyright (C) 2009-2013 beingmeta, inc.
   This file provides for HTML documents using KNODULES, including
   the extraction and processing of embedded KNODULE definitions
   or references and interaction with interactive parts of the
   FDJT library.

   For more information on knodules, visit www.knodules.net
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

    var fdjtString=fdjt.String;
    var fdjtLog=fdjt.Log;
    var fdjtDOM=fdjt.DOM;
    var fdjtUI=fdjt.UI;
    var fdjtKB=fdjt.KB, fdjtID=fdjt.ID;

    var addClass=fdjtDOM.addClass;

    /* Getting knowdes into HTML */

    var KNode=Knodule.KNode;
    Knodule.KNode.prototype.toDOM=
        Knodule.KNode.prototype.toHTML=function(lang){
            var spec=((this.prime)?("span.dterm.prime"):
                      (this.weak)?("span.dterm.weak"):
                      "span.dterm");
            var span=fdjtDOM(spec,this.dterm);
            if (this.gloss) 
                span.title=fdjtString.strip_markup(this.gloss);
            span.dterm=this.dterm;
            return span;};
    
    /* Making DTERM descriptions */

    function html2dom(html){
        if (!(html)) return false;
        else if (typeof html === 'string') {
            if (html[0]==='<') return fdjtDOM(html);
            else fdjtDOM("span",html);}
        else return html;}

    function knoduleHTML(arg,knodule,varname,lang){
        var checkbox=false; var variations=[];
        var knode=false, text=false, tag=false, title=false;
        var def=false, obj=false;
        // If needed, provide a default knodule based on the current
        // document
        var default_knodule=knodule||Kindule.current||
            (Knodule.current=(new Knodule(location.href)));
        if (typeof arg === 'string') {
            // Try to convert a string arg into a knode
            if (arg.indexOf('|')>0) {
                // We'll save the def to attach to any tag string
                var pos=arg.indexOf('|'); def=arg.slice(pos);
                obj=knode=default_knodule.handleSubjectEntry(arg);}
            else if (arg.indexOf('@')>0)
                obj=knode=default_knodule.ref(arg);
            else knode=default_knodule.probe(arg);}
        else if (arg instanceof KNode) obj=knode=arg;
        else obj=arg;
        if ((knode)&&(!(knode._init))) knode.load();
        // A non-false language arg means generate a FDJT completion
        // node; if the language arg isn't a string, just use the
        // default knodule's default language to generate the text.
        if ((lang)&&(typeof lang !== 'string')) {
            if (default_knodule) lang=default_knodule.language;
            else lang='EN';}
        // This figures out the core text for the DOM node which is
        // returned.
        text=((knode)?
              // This should probably look for a dterm in the target
              // language, but we'll skip that for now
              (knode.dterm):
              ((obj)?
               // Use the toHuman, toDOM, and toHTML methods when
               // available (in that order)
               (((obj.toDOM)&&(obj.toDOM()))||
                ((obj.toHTML)&&(html2dom(obj.toHTML())))||
                ((obj.toHuman)&&(html2dom(obj.toHuman(lang))))||
                obj.name||obj._name||obj._id||obj):
               arg));
        if ((knode)&&(knode.literal)) text="“"+text+"”";
        // Figure out the 'tag' which is a string reference to the
        //  value
        tag=((obj)&&(obj.tagString)&&(obj.tagString()))||
            ((knode)&&(knode._db===knodule)&&(knode.dterm))||
            ((knode)&&(knode.dterm+"@"+knode._db.name))||
            (obj._qid)||(obj.oid)||(obj.uuid)||
            ((obj._id)&&(obj._db.absrefs)&&(obj._id))||
            ((obj._id)&&(obj._domain)&&(obj._id+"@"+obj._domain));
        if ((tag)&&(def)) tag=tag+def;
        if ((varname)&&(tag)) {
            checkbox=fdjtDOM(
                {tagName: "INPUT",type: "CHECKBOX",
                 name: varname,value: tag});}
        // Add variations for synonyms in the given language.
        if ((lang)&&(knode)) {
            var dterm=knode.dterm;
            var synonyms=knode[lang];
            if ((synonyms)&&(typeof synonyms === 'string'))
                synonyms=[synonyms];
            if (synonyms) {
                var i=0; while (i<synonyms.length) {
                    var synonym=synonyms[i++];
                    if (synonym===dterm) continue;
                    var variation=fdjtDOM("span.variation",synonym,"=");
                    variation.setAttribute("key",synonym);
                    variations.push(variation);}}}
        // This is the actual returned DOM node
        var span=fdjtDOM("span",checkbox,variations,text);
        // Declare as a dterm
        if (knode) addClass(span,"dterm");
        // Say if it's a "weak" dterm
        if ((knode)&&(knode.weak)) addClass(span,"weak");
        // Set up as a clickable checkspan
        if (varname) addClass(span,"checkspan");
        if (lang) {
            // Set up as a FDJT completion
            fdjtDOM.addClass(span,"completion");
            if (typeof text === 'string')
                span.setAttribute('key',text);
            else if ((obj)&&(obj.dterm))
                span.setAttribute('key',obj.dterm);
            else if ((obj)&&(obj.name))
                span.setAttribute('key',obj.name);
            else if (tag) span.setAttribute('key',tag);
            else {}
            if (tag) span.setAttribute('value',tag);}
        if (!(knode)) fdjtDOM.addClass(span,"rawterm");
        var from=(((knode)&&(knode._db.description))?
                  (" (from "+knode._db.description+")"):(""))
        if ((knode)&&(knode.gloss)) title=knode.gloss+from;
        else if ((knode)&&(knode.about)) title=knode.about+from;
        else if ((obj)&&(obj.about)) title=obj.about+from;
        else if ((knode)&&(knode.dterm)) title=knode.dterm+from;
        else if (tag) title=tag+from;
        else {}
        if ((knode)&&(knode._always)) {
            var seen={};
            var always=knode._always;
            var i=0, lim=always.length;
            while (i<lim) {
                var a=always[i++];
                if (seen[a._qid]) continue;
                title=title+" ^"+a.dterm;}}
        if (tag) span.setAttribute('tag',tag);
        span.title=title;
        return span;};
    Knodule.HTML=knoduleHTML;
    Knodule.prototype.HTML=function(dterm){
        var args=new Array(arguments.length+1);
        args[0]=arguments[0]; args[1]=this;
        var i=1; var lim=arguments.length; while (i<lim) {
            args[i+1]=arguments[i]; i++;}
        return knoduleHTML.apply(this,args);};

    /* Getting Knodules out of HTML */

    var _knodulesHTML_done=false;

    function KnoduleLoad(elt,knodule){
        var src=((typeof elt === 'string')?(elt):(elt.src));
        var text=fdjtAjax.getText(src);
        var knowdes=knodule.handleEntries(text);
        if ((knodule.trace_load)||(Knodule.trace_load))
            fdjtLog("Parsed %d entries from %s",knowdes.length,elt.src);}

    function knoduleSetupHTML(knodule){
        if (!(knodule)) knodule=Knodule(document.location.href);
        var doing_the_whole_thing=false;
        var start=new Date();
        var links=fdjtDOM.getLinks("SBOOK.knodule",true,true).
            concat(fdjtDOM.getLink("knodule",true,true));
        var i=0; while (i<links.length) KnoduleLoad(links[i++],knodule);
        var elts=fdjtDOM.getMeta("SBOOK.knowdef");
        var i=0; while (i<elts.length) {
            var elt=elts[i++];
            if (elt.name==="KNOWDEF") knodule.handleEntry(elt.content);}
        elts=document.getElementsByTagName("META");
        var i=0; while (i<elts.length) {
            var elt=elts[i++];
            if (elt.name==="KNOWDEF") knodule.handleEntry(elt.content);}
        elts=document.getElementsByTagName("SCRIPT");
        i=0; while (i<elts.length) {
            var elt=elts[i++];
            var lang=elt.getAttribute("language");
            var type=elt.type;
            if ((type==="text/knodule")||(type==="application/knodule")||
                ((lang) &&
                 ((lang==="knodule") ||(lang==="KNODULE")||
                  (lang==="knowlet"||(lang==="KNOWLET"))))) {
                if (elt.src) KnoduleLoad(elt,knodule);
                else if (elt.text) {
                    var txt=elt.text;
                    var cdata=txt.search("<!\\[CDATA\\[");
                    if (cdata>=0) {
                        var cdend=txt.search("]]>");
                        txt=txt.slice(cdata+9,cdend);}
                    var dterms=knodule.handleEntries(txt);
                    if ((knodule.trace_load)||(Knodule.trace_load))
                        fdjtLog("Parsed %d inline knodule entries",
                                dterms.length);}
                else {}}}
        var finished=new Date();
        if ((knodule.trace_load)||(Knodule.trace_load))
            fdjtLog("Processed knodules in %fs",
                    ((finished.getTime()-start.getTime())/1000));}
    Knodule.HTML.Setup=knoduleSetupHTML;

})();

/* Emacs local variables
   ;;;  Local variables: ***
   ;;;  compile-command: "cd ..; make" ***
   ;;;  indent-tabs-mode: nil ***
   ;;;  End: ***
*/

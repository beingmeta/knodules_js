/* -*- Mode: Javascript; Character-encoding: utf-8; -*- */

/* ##################### knodules/html.js ####################### */

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
    var fdjtID=fdjt.ID;
    var RefDB=fdjt.RefDB, Ref=fdjt.Ref;

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

    function KNode2HTML(arg,knodule,varname,cloud,lang){
        if (cloud===true) {
            if (typeof lang !== "string") lang=(Knodule.language)||"EN";
            cloud=false;}
        else if ((cloud)&&(typeof lang !== "string"))
            lang=(Knodule.language)||"EN";
        else {}
        
        var valstring=((typeof arg === "string")&&(arg))||(arg._qid)||
            ((arg.getQID)&&(arg.getQID()))||(arg.toString());
        var checkbox=((varname)&&
                      (fdjtDOM({tagName: "INPUT",type: "CHECKBOX",
                                name: varname,value: tag})));
        var text=((typeof arg === "string")&&(arg))||
            fdjtDOM("span.term",valstring);
        var variations=((arg instanceof KNode)&&(fdjtDOM("span.variations")));
        var span=fdjtDOM(((typeof arg === "string")?("span.rawterm"):("span.dterm")),
                         checkbox," ",variations,text);
        if ((lang)||(cloud)) {
            addClass(span,"completion")
            span.setAttribute("value",valstring);}
        function init(){
            var db=arg._db; var title="";
            if (arg instanceof KNode) {
                var knode=arg, dterm=knode.dterm;
                text.innerHTML=dterm;
                span.setAttribute("key",dterm);
                if ((lang)||(cloud)) {
                    var synonyms=knode[lang];
                    if ((synonyms)&&(typeof synonyms === 'string'))
                        synonyms=[synonyms];
                    if (synonyms) {
                        var i=0; while (i<synonyms.length) {
                            var synonym=synonyms[i++];
                            if (synonym===dterm) continue;
                            var variation=fdjtDOM("span.variation",synonym,"=");
                            variation.setAttribute("key",synonym);
                            variations.appendChild(variation);}}
                    if (knode.about) span.title=knode.about;
                    // This should try to get a dterm in the right language
                    span.setAttribute("key",knode.dterm);}
                else span.setAttribute("key",knode.dterm);}
            else {
                if (arg.name) {
                    span.setAttribute("key",arg.name);
                    span.innerHTML=arg.name;}}
            if (cloud) cloud.addCompletion(span);}
        if (typeof arg === "string") {
            span.setAttribute("key",arg);
            if (cloud) cloud.addCompletion(span);
            return span;}
        else if (arg._live) {init(); return span;}
        else {arg.onLoad(init); return span;}}

    Knodule.HTML=KNode2HTML;
    Knodule.KNode2HTML=KNode2HTML;
    Knodule.Knode2HTML=KNode2HTML;
    Knodule.knode2HTML=KNode2HTML;

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

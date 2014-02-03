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
/* jshint browser: true */
/* global Knodule: false */

//var fdjt=((window)?((window.fdjt)||(window.fdjt={})):({}));
//var Knodule=window.Knodule;

(function(){
    "use strict";

    var fdjtString=fdjt.String;
    var fdjtLog=fdjt.Log;
    var fdjtDOM=fdjt.DOM;
    var fdjtAjax=fdjt.Ajax;
    
    var addClass=fdjtDOM.addClass;

    /* Getting knowdes into HTML */

    var KNode=Knodule.KNode;
    Knodule.KNode.prototype.toDOM=
        Knodule.KNode.prototype.toHTML=function(){
            var spec=((this.prime)?("span.dterm.prime"):
                      (this.weak)?("span.dterm.weak"):
                      "span.dterm");
            var span=fdjtDOM(spec,this.dterm);
            if (this.gloss) 
                span.title=fdjtString.strip_markup(this.gloss);
            span.dterm=this.dterm;
            return span;};
    
    /* Making DTERM descriptions */

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
                                name: varname,value: valstring})));
        var text=((typeof arg === "string")&&(arg))||
            fdjtDOM("span.term",valstring);
        var variations=((arg instanceof KNode)&&(fdjtDOM("span.variations")));
        var span=fdjtDOM(((typeof arg === "string")?("span.rawterm"):("span.dterm")),
                         checkbox," ",variations,text);
        if ((lang)||(cloud)) {
            addClass(span,"completion");
            span.setAttribute("value",valstring);}
        function init(){
            if (arg instanceof KNode) {
                var knode=arg, dterm=knode.dterm;
                text.innerHTML=dterm;
                span.setAttribute("key",dterm);
                span.setAttribute("data-dterm",knode);
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

    /* Getting Knodules out of HTML */

    function knoduleLoad(elt,knodule){
        var src=((typeof elt === 'string')?(elt):(elt.src));
        var text=fdjtAjax.getText(src);
        var knowdes=knodule.handleEntries(text);
        if ((knodule.trace_load)||(Knodule.trace_load))
            fdjtLog("Parsed %d entries from %s",knowdes.length,elt.src);}

    function knoduleSetupHTML(knodule){
        if (!(knodule)) knodule=new Knodule(document.location.href);
        var start=new Date();
        var elts=fdjtDOM.getLinks("{http://knodules.org/}knodule",true,true);
        var i=0, lim, elt;
        if (!((elts)&&(elts.length)))
            elts=fdjtDOM.getLinks("knodule",true,true);
        if (!((elts)&&(elts.length)))
            elts=fdjtDOM.getLinks("*.knodule",true,true);
        i=0; lim=elts.length; while (i<lim) knoduleLoad(elts[i++],knodule);
        elts=fdjtDOM.getMeta("SBOOKS.knodef");
        i=0; lim=elts.length; while (i<elts.length) {
            elt=elts[i++];
            if (elt.name==="KNODEF") knodule.handleEntry(elt.content);}
        elts=document.getElementsByTagName("META");
        i=0; lim=elts.length; while (i<lim) {
            elt=elts[i++];
            if (elt.name==="KNODEF") knodule.handleEntry(elt.content);}
        elts=document.getElementsByTagName("SCRIPT");
        i=0; lim=elts.length; while (i<lim) {
            elt=elts[i++];
            var lang=elt.getAttribute("language");
            var type=elt.type;
            if ((type==="text/knodule")||(type==="application/knodule")||
                ((lang) &&
                 ((lang==="knodule") ||(lang==="KNODULE")||
                  (lang==="knowlet"||(lang==="KNOWLET"))))) {
                if (elt.src) knoduleLoad(elt,knodule);
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

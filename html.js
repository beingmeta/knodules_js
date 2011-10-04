/* -*- Mode: Javascript; Character-encoding: utf-8; -*- */

/* Copyright (C) 2009-2011 beingmeta, inc.
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

    var knodules_trace_load=2;

    /* Getting knowdes into HTML */

    var KNode=Knodule.KNode;
    Knodule.KNode.prototype.toHTML=function(lang){
	var spec=((this.prime)?("span.dterm.prime"):
		  (this.weak)?("span.dterm.weak"):
		  "span.dterm");
	if (this.gloss) {
	    var span=fdjtDOM(spec,this.dterm);
	    span.title=fdjtString.strip_markup(this.gloss);
	    span.dterm=this.dterm;
	    return span;}
	else return fdjtDOM(spec,this.dterm);};

    /* Making DTERM descriptions */

    function knoduleHTML(dterm,kno,varname,lang){
	var checkbox=false; var variations=[];
	var text=dterm; var def=false;
	// A non-false language arg generates a completion, and a
	// non-string language arg just uses the knodules default language
	if ((lang)&&(typeof lang !== 'string')) {
	    if (kno) lang=kno.language; else lang='EN';}
	// Resolve the KNode if you can
	if ((kno)&&(typeof dterm === 'string'))
	    if (kno.probe(dterm)) {
		dterm=kno.probe(dterm);
		text=dterm.dterm;}
	else if (dterm.indexOf('|')>=0) {
	    var pos=dterm.indexOf('|');
	    def=dterm.slice(pos);
	    dterm=kno.handleSubjectEntry(dterm);
	    text=dterm.dterm;}
	else dterm=dterm;
	var tagstring=false;
	if ((varname)||(lang)) {
	    tagstring=((dterm.tagString)?(dterm.tagString()):
		       ((dterm._id)||(dterm)));
	    if (def) tagstring=tagstring+def;}
	if (varname) 
	    checkbox=fdjtDOM
	({tagName: "INPUT",type: "CHECKBOX",name: varname,value: tagstring});
	if ((lang)&&(dterm instanceof KNode)) {
	    var synonyms=dterm[lang];
	    if ((synonyms)&&(typeof synonyms === 'string'))
		synonyms=[synonyms];
	    if (synonyms) {
		var i=0; while (i<synonyms.length) {
		    var synonym=synonyms[i++];
		    if (synonym===dterm) continue;
		    var variation=fdjtDOM("span.variation",synonym,"=");
		    variation.setAttribute("key",synonym);
		    variations.push(variation);}}}
	var span=fdjtDOM("span.knode",checkbox,variations,text);
	if (varname) fdjtDOM.addClass(span,"checkspan");
	if (typeof text !== 'string') text=tagstring;
	if (lang) {
	    fdjtDOM.addClass(span,"completion");
	    span.key=text; span.value=tagstring;}
	if (!(dterm instanceof KNode)) fdjtDOM.addClass(span,"raw");
	if (dterm.gloss) span.title=dterm.gloss;
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
	if (knodules_trace_load)
	    fdjtLog("Parsed %d entries from %s",knowdes.length,elt.src);}

    function knoduleSetupHTML(knodule){
	if (!(knodule)) knodule=Knodule(document.location.href);
	var doing_the_whole_thing=false;
	var start=new Date();
	var links=fdjtDOM.getLink("knodule",true,false).concat
	(fdjtDOM.getLink("knowlet",true,false));
	var i=0; while (i<links.length) KnoduleLoad(links[i++],knodule);
	var elts=document.getElementsByTagName("META");
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
		    if (knodules_trace_load)
			fdjtLog("Parsed %d inline knodule entries",
				dterms.length);}
		else {}}}
	var finished=new Date();
	if (knodules_trace_load)
	    fdjtLog("Processed knodules in %fs",
		    ((finished.getTime()-start.getTime())/1000));}
    Knodule.HTML.Setup=knoduleSetupHTML;

})();

/* Emacs local variables
   ;;;  Local variables: ***
   ;;;  compile-command: "cd ..; make" ***
   ;;;  End: ***
*/

/* -*- Mode: Javascript; -*- */

/* Copyright (C) 2009-2010 beingmeta, inc.
   This file provides for HTML documents using KNOWLETS, including
    the extraction and processing of embedded KNOWLET definitions
    or references and interaction with interactive parts of the
    FDJT library.

   For more information on knowlets, visit www.knowlets.net
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

    var knowlets_trace_load=1;

    /* Getting knowdes into HTML */

    var DTerm=Knowlet.DTerm;
    Knowlet.DTerm.prototype.toHTML=function(lang){
	if (this.gloss) {
	    var span=fdjtDOM("span.dterm",this.dterm);
	    span.title=fdjtString.strip_markup(this.gloss);
	    span.dterm=this.dterm;
	    return span;}
	else return fdjtDOM("span.dterm",this.dterm);};

    /* Making DTERM descriptions */

    function knowletHTML(dterm,kno,varname,lang){
	var checkbox=false; var variations=[];
	var text=dterm; var def=false;
	// A non-false language arg generates a completion, and a
	// non-string language arg just uses the knowlets default language
	if ((lang)&&(typeof lang !== 'string')) {
	    if (kno) lang=kno.language; else lang='EN';}
	// Resolve the DTerm if you can
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
	    tagstring=((dterm.tagString)?(dterm.tagString()):(dterm));
	    if (def) tagstring=tagstring+def;}
	if (varname) 
	    checkbox=fdjtDOM
	({tagName: "INPUT",type: "CHECKBOX",name: varname,value: tagstring});
	if ((lang)&&(dterm instanceof DTerm)) {
	    var synonyms=dterm[lang];
	    if ((synonyms)&&(typeof synonyms === 'string'))
		synonyms=[synonyms];
	    if (synonyms) {
		var i=0; while (i<synonyms.length) {
		    var synonym=synonyms[i++];
		    if (synonym===dterm) continue;
		    var variation=fdjtDOM("span.variation",synonym,"=");
		    variation.key=synonym;
		    variations.push(variation);}}}
	var span=fdjtDOM("span.dterm",checkbox,variations,text);
	if (varname) fdjtDOM.addClass(span,"checkspan");
	if (lang) {
	    fdjtDOM.addClass(span,"completion");
	    span.key=text;
	    span.value=tagstring;}
	if (!(dterm instanceof DTerm)) fdjtDOM.addClass(span,"raw");
	if (dterm.gloss) span.title=dterm.gloss;
	return span;};
    Knowlet.HTML=knowletHTML;
    Knowlet.prototype.HTML=function(dterm){
	var args=new Array(arguments.length+1);
	args[0]=arguments[0]; args[1]=this;
	var i=1; var lim=arguments.length; while (i<lim) {
	    args[i+1]=arguments[i]; i++;}
	return knowletHTML.apply(this,args);};

    /* Getting Knowlets out of HTML */

    var _knowletsHTML_done=false;

    function KnowletLoad(elt,knowlet){
	var text=fdjtAjaxGetText(elt.src);
	var knowdes=knowlet.handleEntries(text);
	if (knowlets_trace_load)
	    fdjtLog("[%fs] Parsed %d entries from %s",fdjtET(),knowdes.length,elt.src);
	if (elt.text) {
	    var more_knowdes=knowlet.handleEntries(elt.text);
	    if (knowlets_trace_load)
		fdjtLog("[%fs] Parsed %d more entries from %s",fdjtET(),knowdes.length);}}

    function knowletSetupHTML(knowlet){
	fdjtLog("Doing HTML setup for %o",knowlet);
	if (!(knowlet))
	    knowlet=Knowlet(document.location.href);
	var doing_the_whole_thing=false;
	var start=new Date();
	var elts=document.getElementsByTagName("META");
	var i=0; while (i<elts.length) {
	    var elt=elts[i++];
	    if (elt.name==="KNOWDEF") knowlet.handleEntry(elt.content);}
	elts=document.getElementsByTagName("SCRIPT");
	i=0; while (i<elts.length) {
	    var elt=elts[i++];
	    if ((elt.getAttribute("language")) &&
		(((elt.getAttribute("language"))==="knowlet") ||
		 ((elt.getAttribute("language"))==="KNOWLET"))) {
		if (elt.src) KnowletLoad(elt,knowlet);
		else if (elt.text) {
		    var dterms=knowlet.handleEntries(elt.text);
		    if (knowlets_trace_load)
			fdjtLog("[%fs] Parsed %d entries from %o",
				fdjtET(),dterms.length,elt);}
		else {}}}
	var finished=new Date();
	if (knowlets_trace_load)
	    fdjtLog("[%fs] Processed knowlets in ",fdjtET(),
		    ((finished.getTime()-start.getTime())/1000)+"s");}
    Knowlet.HTML.Setup=knowletSetupHTML;

})();

/* Emacs local variables
;;;  Local variables: ***
;;;  compile-command: "cd ..; make" ***
;;;  End: ***
*/

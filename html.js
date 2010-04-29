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

var knowlets_trace_load=0;

/* Getting knowdes into HTML */

DTerm.prototype.toHTML=function()
{
  if (this.gloss) {
    var span=fdjtDOM("span.dterm",this.dterm);
    span.title=fdjtString.strip_markup(this.gloss);
    span.dterm=this.dterm;
    return span;}
  else return fdjtDOM("span.dterm",this.dterm);
};

/* Making DTERM descriptions */

var kno_dterm_prefix=false;
var kno_dterm_suffix=false;

function knoSpan(dterm,kno)
{
  if (dterm instanceof DTerm)
    return dterm.toHTML();
  else if (!(typeof dterm === 'string')) return false;
  else if ((kno)&&(kno.probe(dterm)))
    return (kno.probe(dterm)).toHTML();
  else if ((kno)&&(dterm.indexof('|')>0))
    return kno.DTerm(dterm).toHTML();
  else return fdjtDOM("span.dterm.raw",dterm);
}
function knoDTermSpan(dterm,display,kno)
{
  return knoSpan(dterm,kno);
}

/* Extended form elements for Knowdes */

function knoCheckspan(varname,value,checked,kno)
{
  if (!(kno)) kno=window.knowlet||false;
  var checkbox=
    fdjtDOM
    ({tagName: "INPUT",
	type: "CHECKBOX",
	name: name,value: value.tagString(kno)});
  var checkspan=fdjtDOM("span.checkspan",checkbox,knoSpan(value,kno));
  if (checked) {
    checkspan.setAttribute('ischecked','true');
    checkbox.checked=true;}
  else {
    checkbox.checked=false;}
  return checkspan;
}

function knoCompletion(value,kno,lang)
{
  if (!(kno)) kno=window.knowlet||false;
  if (!(lang)) lang=((kno)?(kno.language):('EN'));
  var knospan=knoSpan(value,false,kno||false);
  fdjtDOM.addClass(knospan,"completion");
  if (typeof value === 'string') {
    knospan.value=value; knospan.key=value;
    return knospan;}
  knospan.value=value.tagString(); knospan.key=value.dterm;
  var synonyms=value[lang];
  if (synonyms) {
    var i=0; while (i<synonyms.length) {
      var synonym=synonyms[i++];
      if (synonym===dterm) continue;
      var variant=fdjtSpan("variation",synonym,"=");
      variant.key=synonym;
      fdjtPrepend(knospan,variant);}}
  return knospan;
}

function knoCheckCompletion(varname,value,checked,kno)
{
  var checkspan=knoCompletion(value);
  var tagstring=((typeof value ==='string')?(value):(value.tagString()));
  var checkbox=fdjtInput("CHECKBOX",varname,tagstring);
  checkbox.checked=checked||false;
  fdjtAddClass(checkspan,"checkspan");
  fdjtPrepend(checkspan,checkbox);
  fdjtCheckSpan_setup(checkspan);
  return checkspan;
}

/* Getting Knowlets out of HTML */

var _knowletsHTML_done=false;

function KnowletLoad(elt)
{
  var text=fdjtAjaxGetText(elt.src);
  var knowdes=knowlet.handleEntries(text);
  if (knowlets_trace_load)
    fdjtLog("[%fs] Parsed %d entries from %s",fdjtET(),knowdes.length,elt.src);
  if (elt.text) {
    var more_knowdes=knowlet.handleEntries(elt.text);
    if (knowlets_trace_load)
      fdjtLog("[%fs] Parsed %d more entries from %s",fdjtET(),knowdes.length);}
}

function knowletSetupHTML(knowlet)
{
  if (!(knowlet))
    knowlet=document.knowlet||
      Knowlet(document.location.href);
  var doing_the_whole_thing=false;
  var start=new Date();
  var elts=document.getElementsByTagName("META");
  var i=0; while (i<elts.length) {
    var elt=elts[i++];
    if (elt.name==="KNOWDEF") knowlet.handleEntry(elt.content);}
  elts=document.getElementsByTagName(document,"SCRIPT");
  i=0; while (i<elts.length) {
    var elt=elts[i++];
    if ((elt.getAttribute("language")) &&
	(((elt.getAttribute("language"))==="knowlet") ||
	 ((elt.getAttribute("language"))==="KNOWLET"))) {
      if (elt.src) KnowletLoad(elt);
      else if (elt.text) {
	var dterms=knowlet.handleEntries(elt.text);
	if (knowlets_trace_load)
	  fdjtLog("[%fs] Parsed %d entries from %o",
		  fdjt.ET(),dterms.length,elt);}
      else {}}}
  var finished=new Date();
  if (knowlets_trace_load)
    fdjtLog("[%fs] Processed knowlets in ",
	    ((finished.getTime()-start.getTime())/1000)+"s",
	    fdjt.ET());
}

/* Emacs local variables
;;;  Local variables: ***
;;;  compile-command: "cd ..; make" ***
;;;  End: ***
*/

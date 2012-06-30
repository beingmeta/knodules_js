/* -*- Mode: Javascript; Character-encoding: utf-8; -*- */

/* ##################### knodules/clouds.js ####################### */

/* Copyright (C) 2009-2012 beingmeta, inc.
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
     
     function KNodeCompletion(index,term,title,just_knodes){
	 var knodule=index.knodule;
	 var showname=term;
	 if ((typeof term === "string") && (term[0]==="\u00A7")) {
	     if (showname.length>20) {
		 var start=showname.indexOf(' ',8);
		 var end=showname.lastIndexOf(' ',showname.length-8);
		 if (start<0) start=8; if (end<0) end=showname.length-8;
		 if (start<(showname.length-end)) {
		     showname=showname.slice(0,start)+" \u2026 "+
			 showname.slice(end);}
		 title=term;}
	     var span=fdjtDOM("span.completion",
			      fdjtDOM("span.sectname",showname));
	     span.key=term; span.value=term; span.anymatch=true;
	     if (title)
		 span.title=title+"; "+term;
	     else span.title=""+index.freq(term)+" items: "+term;
	     return span;}
	 var ref=knodule.probe(term)||fdjtKB.ref(term);
	 var text=((ref)?(ref.dterm):(term));
	 if (!(ref)) {
	     if (just_knodes) return false;
	     var knopos=term.indexOf('@');
	     if ((knopos>0)&&(term.slice(1+knopos)===knodule.name)) {
		 if (title) title="("+term+") "+title; else title=term;
		 text=term.slice(0,knopos);}}
	 else if (!(ref.dterm)) {
	     fdjtLog("Got bogus dterm reference for %s: %o",term,ref);
	     ref=false;}
	 var term_node=((ref) ?
			(((ref.toDOM)&&(ref.toDOM()))||
			 ((ref.toHTML)&&(ref.toHTML()))) :
			(fdjtDOM("span.rawterm",showterm)));
	 if ((ref)&&(fdjtString.hasSuffix(ref.dterm,"...")))
	     addClass(term_node,"weak");
	 var span=fdjtDOM("span.completion");
	 if (ref) {
	     if ((ref.gloss)||(ref.about))
		 span.title=((title)||"")+(ref.gloss||ref.about||"");
	     else if (title) span.title=title;
	     else {}
	     /* Now add variation elements */
	     var variations=[];
	     var i=0; var terms=dterm.getSet('EN');
	     while (i<terms.length) {
		 var term=terms[i++];
		 if (term===dterm.dterm) continue;
		 var vary=fdjtDOM("span.variation",term);
		 vary.key=term;
		 span.appendChild(vary);
		 span.appendChild(document.createTextNode(" "));}
	     span.appendChild(term_node);
	     span.setAttribute(
		 "value",((dterm.tagString)?(dterm.tagString()):(dterm.dterm)));
	     span.setAttribute("dterm",dterm.dterm);}
	 else {
	     span.setAttribute("key",term);
	     span.setAttribute("value",term);
	     span.appendChild(term_node);
	     if (title) span.title=title;}
	 return span;}

     KnoduleIndex.prototype.makeCloud=function(
	 dterms,scores,freqs,ranks_arg,noscale,ontap,onchange) {
	 var index=this; var knodule=index.knodule;
	 var primescores=((knodule)&&(knodule.primescores));
	 var start=new Date();
	 var n_terms=dterms.length;
	 var i=0, max_score=0, min_score=false, primecues=0;
	 if (scores) {
	     var i=0; while (i<dterms.length) {
		 var dterm=dterms[i++];
		 if (primescores[dterm]) primecues++;
		 var score=scores[dterm];
		 if (score) {
		     if (min_score===false) min_score=score;
		     else if (score<min_score) min_score=score;
		     if (score>max_score) max_score=score;}}}
	 if (index.trace_clouds)
	     fdjtLog("Making cloud from %d dterms using scores=%o [%d,%d] and freqs=%o",
		     dterms.length,scores,max_score,min_score,freqs);
	 // We show cues if there are too many terms and we would have
	 //  any cues to show Cues are either primescores or higher
	 //  scored items
	 var usecues=(!((n_terms<17)||
			((max_score===min_score)&&(primescores===0))));
	 var spans=fdjtDOM("span");
	 var showall=(usecues)&&
	     fdjtDOM("span.showall",
		     fdjtDOM("span.showmore","more"),
		     fdjtDOM("span.showless","less"));
	 var completions=fdjtDOM("div.completions",showall,spans);
	 if (showall)
	     showall.onclick=function(evt){
		 fdjtDOM.toggleClass(completions,"showempty");
		 if (onchange) onchange(completions);};
	 else fdjtDOM.addClass(completions,"showempty");
	 var copied=[].concat(dterms);
	 var ranks=(((ranks_arg===true)||(typeof ranks_arg==='undefined'))?
		    (index.rankTags()):
		    (ranks_arg));
	 // We sort the keys by absolute frequency
	 if (ranks===false) copied.sort();
	 else copied.sort(function (x,y) {
			      var xrank=ranks[x]||0;
			      var yrank=ranks[y]||0;
			      if (xrank===yrank) {
				  if (x<y) return -1;
				  else if (x===y) return 0;
				  else return 1;}
			      else if (xrank<yrank) return -1;
			      else return 1;});
	 var nspans=0; var sumscale=0;
	 var minscale=false; var maxscale=false;
	 var domnodes=[]; var nodescales=[];
	 var count=scores._count;
	 var cuelim=scores._maxscore/2;
	 var cscores=index.tagscores;
	 var cfreqs=index.tagfreqs;
	 var ctotal=index._allitems.length;
 	 i=0; while (i<copied.length) {
	     var dterm=copied[i++];
	     var freq=freqs[dterm]||1;
	     var cfreq=cfreqs[dterm]||1;
	     var score=scores[dterm]||freq;
	     var scaling=Math.sqrt(score);
	     var title=((freq===cfreq)?
			("score="+score+"; "+freq+" items"):
			("score="+score+"; "+freq+"/"+cfreq+" items"));
	     var span=KNodeCompletion(dterm,title,false);
	     if (!(span)) continue;
	     if (freq===1) addClass(span,"singleton");
	     if ((usecues)&&
		 ((primescores[dterm])||
		  ((scores[dterm])&&(max_score>min_score)&&
		   (scores[dterm]>min_score))))
		 addClass(span,"cue");
	     domnodes.push(span);
	     if ((scores)&&(!(noscale))) {
		 if ((!(minscale))||(scaling<minscale)) minscale=scaling;
		 if ((!(maxscale))||(scaling>maxscale)) maxscale=scaling;
		 nodescales.push(scaling);}
	     fdjtDOM(spans,span,"\n");}
	 // fdjtLog("minscale=%o, maxscale=%o",minscale,maxscale);
	 if (nodescales.length) {
	     var j=0; var jlim=domnodes.length;
	     var scalespan=maxscale-minscale;
	     while (j<jlim) {
		 var node=domnodes[j];
		 var scale=nodescales[j];
		 node.style.fontSize=(100+(100*((scale-minscale)/scalespan)))+'%';
		 j++;}}
	 var maxmsg=fdjtDOM
	 ("div.maxcompletemsg",
	  "There are a lot ","(",fdjtDOM("span.completioncount","really"),")",
	  " of completions.  ");
	 fdjtDOM.prepend(completions,maxmsg);
	 var end=new Date();
	 if (index.Trace.clouds)
	     fdjtLog("Made cloud for %d dterms in %f seconds",
		     dterms.length,(end.getTime()-start.getTime())/1000);

	 if (ontap) completions.onclick=ontap;

	 return completions;};

     function showempty_ontap(evt){
	 var target=fdjtUI.T(evt);
	 var completions=fdjtDOM.getParent(target,".completions");
	 if (completions) {
	     fdjtDOM.toggleClass(completions,"showempty");
	     Codex.UI.updateScroller(completions);}}
     
     KnoduleIndex.prototype.fullCloud=function(ontap,onchange){
	 if (this.full_cloud) return this.full_cloud;
	 else {
	     var tagscores=this.tagscores;
	     var alltags=this._alltags;
	     var tagfreqs=this.tagfreqs;
	     var completions=this.makeCloud(
		 alltags,tagscores,tagfreqs,true,ontap,onchange);
	     var cues=fdjtDOM.getChildren(completions,".cue");
	     this.full_cloud=new fdjtUI.Completions(completions);
	     return this.full_cloud;}};

     KnoduleIndex.Query.prototype.getCloud=function(){
	 if (query._cloud) return query._cloud;
	 else if ((query._query.length)===0) {
	     query._cloud=fullCloud();
	     return query._cloud;}
	 else if (!(query._refiners)) {
	     query._cloud=Codex.empty_cloud;
	     return query._cloud;}
	 else {
	     var refiners=query._refiners;
	     var completions=makeCloud(
		 refiners._results,refiners,refiners._freqs);
	     completions.onclick=cloud_ontap;
	     var n_refiners=query._refiners._results.length;
	     var hide_some=(n_refiners>Codex.show_refiners);
	     if (hide_some) {
		 var cues=fdjtDOM.$(".cue",completions);
		 if (!((cues)&&(cues.length))) {
		     var compelts=fdjtDOM.$(".completion",completions);
		     var i=0; var lim=((compelts.length<Codex.show_refiners)?
				       (compelts.length):(Codex.show_refiners));
		     while (i<lim) addClass(compelts[i++],"cue");}}
	     else addClass(completions,"showempty");
	     query._cloud=
		 new fdjtUI.Completions(completions,fdjtID("CODEXSEARCHINPUT"));
	     return query._cloud;}};

 })();


/* Emacs local variables
   ;;;  Local variables: ***
   ;;;  compile-command: "cd ..; make" ***
   ;;;  End: ***
*/

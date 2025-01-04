////////////////////////////////////////
// 変数
////////////////////////////////////////
const scale_w = 1.0;
const scale_H = 0.7;
const radius_point = 10.0;
let geometric_graph_type = 'RB3-Tree';
let flag_kougo=1;	// 1:赤点青点を交互に打つモード
let nowcolor=0;		// 次に打ったときの点の色
let Nof_colors = 2;			//色数
let n_ithcolor = [];	//色毎の点数
let points = [];				//点集合
let segments = [];			//描画する線分の集合
let convexhull;
let rbmatching;
let threetree;
let depth = 0;

////////////////////////////////////////
// 関数
////////////////////////////////////////
document.addEventListener('DOMContentLoaded', function(){
	document.getElementById('SelectGG').addEventListener('click', function(){change();}, false);
}, false);

let change = () => {
	geometric_graph_type = document.getElementById('SelectGG').value;
	switch(geometric_graph_type){
		case 'conv':
		segments = convexhull.ss;
		break;
		case 'RBMatchings':
		segments = rbmatching.ss;
		break;
		case 'RB3-Tree':
		segments = threetree.ss;
		break;
		default:
		break;
	}
}

let reset = () => {
	for(let i = 0; i < Nof_colors; i++){
		n_ithcolor[i] = 0;
	}
	nowcolor = 0;
	points.length = 0;
	convexhull.reset();
	rbmatching.reset();
	threetree.reset();
	segments.length = 0;
	flag_kougo = 1;
	for(let s of segments){
		s.sw = 1;
	}
}

let kousahantei = (a,b,c,d) => {
	let p = (c.x - d.x)*(a.y - c.y) + (c.y - d.y)*(c.x - a.x);
	let q = (c.x - d.x)*(b.y - c.y) + (c.y - d.y)*(c.x - b.x);
	let r = (a.x - b.x)*(c.y - a.y) + (a.y - b.y)*(a.x - c.x);
	let s = (a.x - b.x)*(d.y - a.y) + (a.y - b.y)*(a.x - d.x);
	return !(r*s < 0 && p*q < 0);
}

// Xの点たちが一般の位置にあるかどうか判定
// 点pが置かれる度に、すでに置かれた点たちが作る直線のいずれにも載らないことを判定
let generalposition = (X) => {
	let slopes = [];
	let p = X[X.length-1];
	for(let i = 0; i < X.length-1; i++){
		if(p.x != X[i].x){
			slopes.push((p.y - X[i].y)/(p.x - X[i].x));
		}
		else if(p.y != X[i].y){
			slopes.push(Infinity);
		}
		else{
			return false;
		}
	}
	if(slopes.length >= 2){
		slopes.sort(function(p,q){return p-q;});
		for(let i = 0; i < slopes.length-1; i++){
			if(slopes[i] === slopes[i+1]){
				return false;
			}
		}
	}
	return true;
}

//Xを3つのクラスR,B,G（|R|>=|B|>=|G|）にバランスよく分類する
//同じ色の点は全て同じクラスに分類される
//Xのどの色の点数も|X|/2の切り上げ以下ならば|R|,|B|,|G|も|X|/2の切り上げ以下となる
//加納・鈴木・宇野の論文のLemma1.9
let intoRBG = (X) => {
	let R = [];
	let B = [];
	let G = [];
	let colortable = [];
	let nr = new Set();
	let nb = 0;
	let r = 0;
	let j = 0;
	for(let p of X){
		let index = colortable.findIndex(function(value){return value[0] === p.color;});
		if(index === -1){
			colortable.push([p.color,1]);
		}
		else{
			colortable[index][1]++;
		}
	}
	if(colortable.length < 2){
		return([X, [], []]);
	}
	colortable.sort(function(p,q){return p[1]-q[1];});
	r = colortable[0][1];
	nr.add(colortable[0][0]);
	while(r + colortable[j+1][1] < Math.floor(X.length/2)){
		j++;
		r = r + colortable[j][1];
		nr.add(colortable[j][0]);
	}
	if(j<colortable.length-1){
		nb = colortable[j+1][0];
	}
	for(let p of X){
		if(nr.has(p.color)){
			R.push(p);
		}
		else if(p.color === nb){
			B.push(p);
		}
		else{
			G.push(p);
		}
	}
	let tempR,tempB,tempG;
	if(R.length === Math.max(R.length,B.length,G.length)){
		tempR = R;
		if(B.length === Math.max(B.length,G.length)){
			tempB = B;
			tempG = G;
		}
		else{
			tempB = G;
			tempG = B;
		}
	}
	else if(B.length === Math.max(B.length,G.length)){
		tempR = B;
		if(R.length === Math.max(R.length,G.length)){
			tempB = R;
			tempG = G;
		}
		else{
			tempB = G;
			tempG = R;
		}
	}
	else{
		tempR = G;
		if(R.length === Math.max(R.length,B.length)){
			tempB = R;
			tempG = B;
		}
		else{
			tempB = B;
			tempG = R;
		}
	}
	return [tempR,tempB,tempG];
}

//3色点列Xのバランスパーティション（加納・鈴木・宇野の補題）
let partition = (X) => {
	let R = [];
	let B = [];
	let G = [];
	[R, B, G] = intoRBG(X);
	let n = X.length;
	let r = 0;
	let b = 0;
	let g = 0;
	let flag;
	if(
		n >= 3 &&
		X[0].color === X[n-1].color &&
		R.length <= Math.ceil(n/2) &&
		B.length <= Math.ceil(n/2) &&
		G.length <= Math.ceil(n/2)
	){
		for(let p = 0; p < n; p++){
			if(R.includes(X[p])){
				r++;
				flag = !(R.includes(X[0]));
			}
			else if(B.includes(X[p])){
				b++;
				flag = !(B.includes(X[0]));
			}
			else{
				g++;
				flag = !(G.includes(X[0]));
			}
			if(
				flag &&
				(p+1)%2 === 0 &&
				2 <= p+1 &&
				p+1 <= n-1 &&
				r <= (p+1)/2 &&
				b <= (p+1)/2 &&
				g <= (p+1)/2 &&
				R.length-r <= Math.ceil((n-(p+1))/2) &&
				B.length-b <= Math.ceil((n-(p+1))/2) &&
				G.length-g <= Math.ceil((n-(p+1))/2)
			)
			return p;
		}
	}
	console.log("X(↓)が補題の前提条件を満たしていません。");
	console.table(X);
	return false;
}

// 基準点X[0]を原点とする複素座標系でX[1]以降を偏角θで環状ソート
// ソート開始点X[1]をX[0].neighbors[1]にした環状ソート
let theta_sort = (X) => {
	for(let p of X){
		if(p === X[0]){
			p.theta = -Infinity;
		}
		else{
			p.theta = Math.atan2(p.y - X[0].y, p.x - X[0].x);
		}
	}
	let p_1 = X[1];
	X.sort(function(p,q){return p.theta - q.theta;});
	//ソート後は基準点X[0]がXの先頭に来ていることに注意して以下を読む

	//ソート後のXを p_0,temp,新Xの３つに分割する
	let p_0 = X.shift();
	let temp = X.splice(0, X.indexOf(p_1)+1);

	//p_0,新X,tempの順に並ぶように結合する
	X.unshift(p_0);
	for(let i = 0; i < temp.length; i++){
		X.push(temp[i]);
	}
}


////////////////////////////////////////
// クラス
////////////////////////////////////////
class Button {
	constructor(w, h, radius, color, text){
		this.x = w;
		this.y = h;
		this.r = radius;
		this.c = color;
		this.text = text;
	}
	resize(w,h){
		this.x = w;
		this.y = h;
	}
	update(){
		noStroke();
		fill(this.c);
		ellipse(this.x, this.y, 2*this.r, 2*this.r);
		fill(255,255,255);
		textSize(36);
		textAlign(CENTER,CENTER);
		text(this.text, this.x, this.y);
	}
	over(){
		if(sq(mouseX - this.x) + sq(mouseY - this.y) < sq(this.r)){
			return true;
		}
		else return false;
	}
}

class Point {
	constructor(x, y, radius, color, number){
		this.x = x;
		this.y = y;
		this.r = radius;
		this.color = color;		//0:赤, 1:青, 2:緑, 3:黄, etc.
		this.number = number;
		this.theta = 0;				//ある基準点を中心とした複素座標系での偏角θ
		points.push(this);
		if(!generalposition(points)){
			points.pop();
		}
		else{
			n_ithcolor[this.color]++;
			if(flag_kougo == 1){
				nowcolor = (nowcolor+1) % Nof_colors;
			}
		}
	}
	update(){
		noStroke();
		switch(this.color){
			case 0:
			fill(255,0,0);
			break;
			case 1:
			fill(0,0,255);
			break;
		}
		ellipse(this.x, this.y, 2*this.r, 2*this.r);
		fill(255,255,255);
		textSize(10);
		textAlign(CENTER,CENTER);
		text(this.number, this.x, this.y);
	}
}

class Segment {
	constructor(p, q, strokeweight){
		this.p = p;
		this.q = q;
		this.sw = strokeweight;
	}
	update(){
		stroke(this.sw,5*this.sw,this.sw);
		line(this.p.x, this.p.y, this.q.x, this.q.y);
	}
}

class ConvexHull {
	constructor(){
		this.vs = [];	//求めた凸包の頂点集合(vertices)
		this.ss = [];	//求めた凸包の線分集合(segments)
	}
	//凸包を求める（Andrew 1979 & アルゴリズムクイックリファレンス参照）
	conv(X){
		this.vs.length = 0;
		this.ss.length = 0;
		X.sort(function(p,q){return p.y - q.y;});
		X.sort(function(p,q){return p.x - q.x;});
		if(X.length < 4){
			for(let p of X){
				this.vs.push(p);
			}
		}
		else{
			this.vs.push(X[0]);
			this.vs.push(X[1]);
			for(let i = 2; i < X.length; i++){
				this.vs.push(X[i]);
				let t = this.vs.length-1;
				while(this.vs.length >= 3 && (this.vs[t-1].x - this.vs[t-2].x)*(this.vs[t].y - this.vs[t-2].y) - (this.vs[t-1].y - this.vs[t-2].y)*(this.vs[t].x - this.vs[t-2].x) >= 0){
					this.vs[t-1] = this.vs[t];
					this.vs.pop();
					t = this.vs.length-1;
				}
			}
			this.vs.push(X[X.length-2]);
			for(let i = X.length-3; i >= 0; i--){
				this.vs.push(X[i]);
				let t = this.vs.length-1;
				while(this.vs.length >= 3 && (this.vs[t-1].x - this.vs[t-2].x)*(this.vs[t].y - this.vs[t-2].y) - (this.vs[t-1].y - this.vs[t-2].y)*(this.vs[t].x - this.vs[t-2].x) >= 0){
					this.vs[t-1] = this.vs[t];
					this.vs.pop();
					t = this.vs.length-1;
				}
			}
			this.vs.pop(); //this.vsの始点と終点が重複するので終点を削除
		}
		for(let i = 0; i < this.vs.length; i++){
			this.ss.push(new Segment(this.vs[i], this.vs[(i+1)%this.vs.length], 1));
		}
		return 0;
	}
	//vが凸包の頂点かどうか判定
	check(v){
		for(let p of this.vs){
			if(p === v){
				return true;
			}
			else{
				return false;
			}
		}
	}
	//vの両隣の頂点を得る
	neighbors(v){
		let N = [];
		let i = this.vs.indexOf(v);
		N.push(this.vs[(this.vs.length + i-1)%this.vs.length]);
		N.push(this.vs[(i+1)%this.vs.length]);
		return N;
	}
	reset(){
		this.vs.length = 0;
		this.ss.length = 0;
	}
}

class RBMatching {
	constructor(){
		this.ss = [];	//X上の無交差交互マッチング(segments)
		this.ch = new ConvexHull();
	}
	//無交差交互マッチングを求める（再帰版）
	matching(X){
		//無交差交互マッチングの存在条件をチェック
		if(X.length === 0 || X.length % 2 !== 0 || n_ithcolor[0] !== n_ithcolor[1]){
			return 0;
		}
		//let X = X_original.concat();
		this.ch.reset();
		this.ch.conv(X);
		let v = this.ch.vs[0];	//x座標が最小の点を選んだことになる
		let a = this.ch.neighbors(v)[0];
		let b = this.ch.neighbors(v)[1];
		if(v.color !== a.color){
			this.ss.push(new Segment(v,a,1));
			X.splice(X.indexOf(v),1);
			X.splice(X.indexOf(a),1);
			this.matching(X);
		}
		else if(v.color !== b.color){
			this.ss.push(new Segment(v,b,1));
			X.splice(X.indexOf(v),1);
			X.splice(X.indexOf(b),1);
			this.matching(X);
		}
		else{
			X.splice(X.indexOf(v),1);
			X.splice(X.indexOf(b),1);
			X.unshift(b);
			X.unshift(v);
			theta_sort(X);
			//ソート後はvがXの先頭に来ていることに注意して以下を読む
			let p = partition(X);
			if(p === false){
				console.log('partirionがfalseを返しました（ありえないのでプログラムにバグがあります）');
				return 0;
			}
			this.ss.push(new Segment(v,X[p],1));
			let X1 = [];	//バランスパーティション後の点集合その１
			let X2 = [];	//バランスパーティション後の点集合その２
			for(let i = 1; i < X.length; i++){	//vは含めないのでi=1から始める
				if(i < p){
					X1.push(X[i]);
				}
				else if(i > p){
					X2.push(X[i]);
				}
			}
			this.matching(X1);
			this.matching(X2);
		}
		return 0;
	}
	reset(){
		this.ss.length = 0;
		this.ch.reset();
	}
}

class ThreeTree {
	constructor(){
		this.ss = [];	//X上の無交差交互3-tree(segments)
		this.ch = new ConvexHull();
	}
	//無交差交互3-treeを求める（赤点青点の点数差を2まで許す版）
	ttree(X,R,B,G,v){
		depth++;
		console.log(`ttreeの深さ:${depth}`);
		console.log(v);
		// console.table(X);
		// console.table(R);
		// console.table(B);
		//論文の定理にある条件(i)が成り立つケース
		if(B.length === 1 && 1 <= R.length && R.length <= 3 && R.includes(v)){
			for(let u of R){
				this.ss.push(new Segment(B[0],u,depth));
			}
			return 0;
		}
		//赤2点青2点のケース
		else if(R.length === 2 && B.length === 2){
			let a,b,c;
			if(kousahantei(R[0],B[0],R[1],B[1])){
				this.ss.push(new Segment(R[0],B[0],depth));
				this.ss.push(new Segment(R[1],B[1],depth));
				if(R[0] === v){
					a = B[0];
					b = R[1];
					c = B[1];
				}
				else{
					a = B[1];
					b = R[0];
					c = B[0];
				}
			}
			else{
				this.ss.push(new Segment(R[0],B[1],depth));
				this.ss.push(new Segment(R[1],B[0],depth));
				if(R[0] === v){
					a = B[1];
					b = R[1];
					c = B[0];
				}
				else{
					a = B[0];
					b = R[0];
					c = B[1];
				}
			}
			this.ss.push(new Segment(a,b,depth));
			return 0;
		}
		//論文の定理にある条件(ii)または(iii)が成り立つケース
		else if(
			(2 <= B.length && R.length === B.length+2 && R.includes(v)) ||
			(2 <= B.length && B.length <= R.length && R.length <= B.length+1)
		){
			let N = [];
			this.ch.reset();
			this.ch.conv(X);
			N = this.ch.neighbors(v);
			// //論文のCase1
			if(N[0].color !== v.color || N[1].color !== v.color){
				let u;
				if(N[0].color !== v.color){
					u = N[0];
				}
				else{
					u = N[1];
				}
				//subcase1.1
				if(2 <= B.length && R.length === B.length+2 && R.includes(v)){
					console.log('case1.1');
					this.ss.push(new Segment(v,u,depth));
					X.splice(X.indexOf(v),1);
					R.splice(R.indexOf(v),1);
					this.ttree(X,R,B,G,u);
					depth--;
				}
				//subcase1.2
				else if(2 <= B.length && B.length <= R.length && R.length <= B.length+1 && R.includes(v)){
					console.log('case1.2');
					this.ss.push(new Segment(v,u,depth));
					X.splice(X.indexOf(v),1);
					R.splice(R.indexOf(v),1);
					this.ttree(X,B,R,G,u);
					depth--;
				}
				//subcase1.3
				else if(2 <= B.length && B.length <= R.length && R.length <= B.length+1 && B.includes(v)){
					console.log('case1.3');
					this.ss.push(new Segment(v,u,depth));
					X.splice(X.indexOf(v),1);
					B.splice(B.indexOf(v),1);
					this.ttree(X,R,B,G,u);
					depth--;
				}
			}
			//論文のCase2
			else{
				let X1 = [];	//バランスパーティション後の点集合その１
				let R1 = [];	//バランスパーティション後の赤点集合その１
				let B1 = [];	//バランスパーティション後の青点集合その１
				let G1 = [];	//バランスパーティション後の緑点集合その１
				let X2 = [];	//バランスパーティション後の点集合その２
				let R2 = [];	//バランスパーティション後の赤点集合その２
				let B2 = [];	//バランスパーティション後の青点集合その２
				let G2 = [];	//バランスパーティション後の緑点集合その２
				X.splice(X.indexOf(v),1);
				X.splice(X.indexOf(this.ch.neighbors(v)[1]),1);
				X.unshift(this.ch.neighbors(v)[1]);
				X.unshift(v);
				theta_sort(X);
				//ソート後はvがXの先頭に来ていることに注意して以下を読む
				let p;
				//subcase2.1
				if(R.includes(v)){
					console.log('case2.1');
					X.splice(X.indexOf(v),1);
					R.splice(R.indexOf(v),1);
					p = partition(X);
					this.ss.push(new Segment(v,X[p],depth));
					for(let i = 0; i < X.length; i++){
						if(i <= p){
							X1.push(X[i]);
							if(R.includes(X[i])){
								R1.push(X[i]);
							}
							else{
								B1.push(X[i]);
							}
						}
						if(i >= p){
							X2.push(X[i]);
							if(R.includes(X[i])){
								R2.push(X[i]);
							}
							else{
								B2.push(X[i]);
							}
						}
					}
					this.ttree(X1,B1,R1,G1,X[p]);
					depth--;
					this.ttree(X2,B2,R2,G2,X[p]);
					depth--;
				}
				//subcase2.2
				else if(B.includes(v)){
					console.log('case2.2');
					p = partition(X);
					this.ss.push(new Segment(v,X[p],depth));
					for(let i = 1; i < X.length; i++){	//vはX[0]にいるのでi=1から開始するとvを無視できる
						if(i <= p){
							X1.push(X[i]);
							if(R.includes(X[i])){
								R1.push(X[i]);
							}
							else{
								B1.push(X[i]);
							}
						}
						if(i >= p){
							X2.push(X[i]);
							if(R.includes(X[i])){
								R2.push(X[i]);
							}
							else{
								B2.push(X[i]);
							}
						}
					}
					this.ttree(X1,R1,B1,G1,X[p]);
					depth--;
					this.ttree(X2,R2,B2,G2,X[p]);
					depth--;
				}
			}
			return 0;
		}
		console.log("X(↓)が定理の前提条件を満たしていません。");
		console.table(X);
		return 0;
	}
	reset(){
		this.ss.length = 0;
		this.ch.reset();
		depth = 0;
	}
}

////////////////////////////////////////
// メイン with p5.js
////////////////////////////////////////
function setup(){
	createCanvas(windowWidth*scale_w,windowHeight*scale_H).parent('p5jsGG');
	alt_botton = new Button(width/8,height-50,40,'#ff00ff','Alt');
	red_botton = new Button(width*2/8,height-50,40,'#ff0000',n_ithcolor[0]);
	blue_botton = new Button(width*3/8,height-50,40,'#0000ff',n_ithcolor[1]);
	convexhull = new ConvexHull();
	rbmatching = new RBMatching();
	threetree = new ThreeTree();
	change();
	reset();
}

function windowResized() {
	width = windowWidth * scale_w;
	height = windowHeight * scale_H;
	resizeCanvas(width, height);
	alt_botton.resize(width/8,height-50);
	red_botton.resize(width*2/8,height-50);
	blue_botton.resize(width*3/8,height-50);
}

function draw(){
	background(255,255,240);
	stroke(0,0,0);
	for(let s of segments){
		s.update();
	}
	for(let p of points){
		p.update();
	}
	alt_botton.update();
	red_botton.text = n_ithcolor[0];
	red_botton.update();
	blue_botton.text = n_ithcolor[1];
	blue_botton.update();
}

function mouseClicked(){
	console.log("------クリックしました--------");
	if(radius_point < mouseX && mouseX < width - radius_point && radius_point < mouseY && mouseY < height - radius_point){
		if(alt_botton.over()){
			flag_kougo = 1;
		}
		else if(red_botton.over()){
			nowcolor = 0;
			flag_kougo = 0;
		}
		else if(blue_botton.over()){
			nowcolor = 1;
			flag_kougo = 0;
		}
		else{
			new Point(mouseX,mouseY,radius_point,nowcolor,points.length+1);
			//凸包を求める
			let X = points.concat();
			convexhull.reset();
			convexhull.conv(X);
			//無交差交互マッチングを求める
			X = points.concat();
			rbmatching.reset();
			rbmatching.matching(X);
			//無交差交互3-treeを求める
			X = points.concat();
			let v = convexhull.vs[0];
			let [R, B, G] = intoRBG(X);
			threetree.reset();
			threetree.ttree(X,R,B,G,v);
		}
	}
}

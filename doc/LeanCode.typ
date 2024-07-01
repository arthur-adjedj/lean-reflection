
#let times = [×]
#let func(x) = text(color.rgb(30, 70, 180))[#x]
#let keyword(x) = text(weight: "bold")[#x]
#let type(x) = text(color.rgb(30, 160, 60) )[#x]
#let ctor(x) = text(color.rgb(120, 160, 30))[#x]
#let decl(x) = x //underline[#x]
#let var(x) = text(style: "italic", x)
#let varb(x) = text(style: "italic", underline(x))
#let tvar(x) = text(style: "italic", type(x))
#let tvarb(x) = text(style: "italic", type(underline(x)))
#let proof(x) = text(color.rgb(180, 10, 180), x)

// Keywords
#let struct = keyword[struct]
#let enum = keyword[enum]
#let fn = keyword[fn]
#let def = keyword[def]
#let structure = keyword[structure]
#let inductive = keyword[inductive]
#let where = keyword[where]
// Notation
#let right = text(font: "Iosevka KiiyaMayThird Extended")[->]
#let mapsto = text(font: "Iosevka KiiyaMayThird Extended")[=>]
#let ind = h(1em)
#let prod = text(font: "Iosevka KiiyaMayThird Extended")[#type(math.times)]

#let code(x) = [
  #set text(font: "Iosevka KiiyaMayThird");
  #show "Type": keyword[Type]
  #show "Prop": keyword[Prop]
  #show "match": keyword[match]
  // Common Types
  #show "String": type[String]
  #show "Nat": type[Nat]
    #show "zero": ctor[zero]
    #show "succ": ctor[succ]
  #show "Person": type[Person]
  #show "Dragon": type[Dragon]
  #show "Fin": type[Fin]
  #show "u32": type[u32]
  #show "Char": type[Char]
  #show "Float": type[Float]
  #show "Option": type[Option]
    #show "Some": ctor[Some]
    #show "None": ctor[None]
    #show "some": ctor[some]
    #show "none": ctor[none]
  #show "Unit": type[Unit]
  #show "List": type[List]
  #show "Vec": type[Vec]
    #show "nil": ctor[nil]
    #show "cons": ctor[cons]
  #show "False": type[False]
  #show "True": type[True]
  #show "And": type[And]
  #show "Either": type[Either]
  #show "Empty": type[Empty]
  #show "Pair": type[Pair]
  #show "DPair": type[DPair]
  #show "Subtype": type[Subtype]
  #show "Exists": type[Exists]
  #show "Or": type[Or]
    #show "left": ctor[left]
    #show "right": ctor[right]
    #show "Left": ctor[Left]
    #show "Right": ctor[Right]
  #show regex("Ty\b"): type[Ty]
  #show regex("TypC\b"): type[TypC]
  #show "Expr": type[Expr]
  #x
]

#let ibox(x) = box(stroke: rgb(40,200,40,255), outset: 0.25em, x)
#let clbox(cl, x) = box(fill: cl, outset: 0.3em, x)
#let rbox(width: 0em, x) = clbox(rgb(255, 0,0, 90), [#h(width/2)#x#h(width/2)])
#let gbox(x) = box(fill: rgb(0,255,0,50), outset: 0.3em, x)
#let bbox(x) = box(fill: rgb(0,0,255,50), outset: 0.3em, x)
#let vecn(n) = text(color.rgb(200,20,120), n)
#let centercodebox(x) = align(center, box[#set align(left); #code[#x]])
// #let hole(x) = box(fill: rgb(0,0,0,30), outset: 0.25em, x)
#let hole(x, width: 0em, color: rgb(0,0,0,16%)) = clbox(color, [#h(width/2)#x#h(width/2)])
#let txt(color: black, x) = text(color, font: "New Computer Modern Sans", x)
// #let txt(x) = text(font: "Comic Sans MS", x)
#let eqv = text(size:1.2em)[$equiv$] // ≣
#let str(x) = text(rgb(180, 100, 50))[\"#x\"]
#let rustbox(color:black.transparentize(95%), x) = box(fill:color, outset: 1em, radius: 0.5em, x)
#let anno(cl, x) = text(cl)[#math.overbrace()[
  #let gap = 0.3em
  #h(gap)#box(fill: cl.transparentize(85%), outset:0.4em, radius: 0.4em)[
    #v(-0.1em)
    #text(black)[#txt[#x]]
  ]#h(gap)
]]

## 你的类型

这个代码库包含了一些类型推理系统的实现，使用语言为 JavaScript。我希望可以通过这个代码库，帮助有志于实现类型推理以及 Term tagging 的人士了解类型系统的基本原理，以及怎样实现它们。

- [HRT.js](https://be5invis.github.io/your-type/hrt.html)：一个支持 Rank-N 类型推理的类型系统。其程序基于 Simon Peyton Jones 等的文献 *[Practical type inference for arbitrary-rank types](http://research.microsoft.com/en-us/um/people/simonpj/papers/higher-rank/putting.pdf)* 改写、扩展而成。输入为一个程序和一个环境，输出此程序返回值类型，以及其经过 Tag 后的 [System F](https://en.wikipedia.org/wiki/System_F) 表达式。


module clinica

----assinaturas---

sig Clinica {
	localizacao: Cidade,
	servicos: set Servico
}

sig Servico {
	profissional: one Profissional}
one sig Odontologia, Psicologia, Fisioterapia extends Servico {}

sig Profissional{}

sig Cidade { clinicas: set Clinica }
one sig CampinaGrande, JoaoPessoa, Patos, SantaRita extends Cidade {}


---predicados---
// não tá rodando esse predicado
/*pred temServico[cli: Clinica, servico: Servico] {
	servico in cli
}*/


---fatos----

fact NumServicosClinica {
	// Cada clínica oferece três serviços.
	all cli: Clinica | #cli.servicos = 3 
}

fact TiposServicos {
	// Os servicos de Odontologia, Psicologia e Fisioterapia estao presentes em toda clinica
	all cli: Clinica | one o: Odontologia | one p: Psicologia | one f: Fisioterapia |
		let ser = cli.servicos | o in ser and p in ser and f in ser
}

fact LocalizacaoClinicas {} // A definir


pred show[]{}
run show for 5

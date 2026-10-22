/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1145 : Family 10 := level10.get ⟨1323,by decide⟩
def sourceMap1145 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1145 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1145_checked : acceptsGraphIso
    (source (graph core1145) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2207.graph sourceMap1145=true := by decide +kernel
theorem fusedMap1145_checked : acceptsGraphIso
    (fused (graph core1145) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1767.graph fusedMap1145=true := by decide +kernel
theorem certified1145 : Certified (graph core1145) (root 10) 2 2 :=
  of_native_maps core1145 DegreeOneMiddleResidualSpectrum2207.graph DegreeOneMiddleResidualSpectrum1767.graph
    sourceMap1145 fusedMap1145 sourceMap1145_checked fusedMap1145_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1145
#print axioms sourceMap1145_checked
#print axioms fusedMap1145_checked
#print axioms certified1145
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

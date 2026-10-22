/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1112 : Family 10 := level10.get ⟨1204,by decide⟩
def sourceMap1112 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1112 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1112_checked : acceptsGraphIso
    (source (graph core1112) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2124.graph sourceMap1112=true := by decide +kernel
theorem fusedMap1112_checked : acceptsGraphIso
    (fused (graph core1112) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1673.graph fusedMap1112=true := by decide +kernel
theorem certified1112 : Certified (graph core1112) (root 10) 2 2 :=
  of_native_maps core1112 DegreeOneMiddleResidualSpectrum2124.graph DegreeOneMiddleResidualSpectrum1673.graph
    sourceMap1112 fusedMap1112 sourceMap1112_checked fusedMap1112_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1112
#print axioms sourceMap1112_checked
#print axioms fusedMap1112_checked
#print axioms certified1112
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

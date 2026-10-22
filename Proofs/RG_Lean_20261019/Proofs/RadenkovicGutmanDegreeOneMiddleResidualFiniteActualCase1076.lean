/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1076 : Family 10 := level10.get ⟨1106,by decide⟩
def sourceMap1076 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1076 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1076_checked : acceptsGraphIso
    (source (graph core1076) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2048.graph sourceMap1076=true := by decide +kernel
theorem fusedMap1076_checked : acceptsGraphIso
    (fused (graph core1076) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1607.graph fusedMap1076=true := by decide +kernel
theorem certified1076 : Certified (graph core1076) (root 10) 2 2 :=
  of_native_maps core1076 DegreeOneMiddleResidualSpectrum2048.graph DegreeOneMiddleResidualSpectrum1607.graph
    sourceMap1076 fusedMap1076 sourceMap1076_checked fusedMap1076_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1076
#print axioms sourceMap1076_checked
#print axioms fusedMap1076_checked
#print axioms certified1076
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

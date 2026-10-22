/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1061 : Family 10 := level10.get ⟨1065,by decide⟩
def sourceMap1061 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1061 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1061_checked : acceptsGraphIso
    (source (graph core1061) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2017.graph sourceMap1061=true := by decide +kernel
theorem fusedMap1061_checked : acceptsGraphIso
    (fused (graph core1061) (root 10) 2 2) DegreeTwoThreeSpectrum6117.graph fusedMap1061=true := by decide +kernel
theorem certified1061 : Certified (graph core1061) (root 10) 2 2 :=
  of_native_maps core1061 DegreeOneMiddleResidualSpectrum2017.graph DegreeTwoThreeSpectrum6117.graph
    sourceMap1061 fusedMap1061 sourceMap1061_checked fusedMap1061_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1061
#print axioms sourceMap1061_checked
#print axioms fusedMap1061_checked
#print axioms certified1061
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

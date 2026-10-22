/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1144 : Family 10 := level10.get ⟨1321,by decide⟩
def sourceMap1144 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1144 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1144_checked : acceptsGraphIso
    (source (graph core1144) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2205.graph sourceMap1144=true := by decide +kernel
theorem fusedMap1144_checked : acceptsGraphIso
    (fused (graph core1144) (root 10) 2 2) DegreeTwoThreeSpectrum6630.graph fusedMap1144=true := by decide +kernel
theorem certified1144 : Certified (graph core1144) (root 10) 2 2 :=
  of_native_maps core1144 DegreeOneMiddleResidualSpectrum2205.graph DegreeTwoThreeSpectrum6630.graph
    sourceMap1144 fusedMap1144 sourceMap1144_checked fusedMap1144_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1144
#print axioms sourceMap1144_checked
#print axioms fusedMap1144_checked
#print axioms certified1144
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1152 : Family 10 := level10.get ⟨1353,by decide⟩
def sourceMap1152 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1152 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1152_checked : acceptsGraphIso
    (source (graph core1152) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2227.graph sourceMap1152=true := by decide +kernel
theorem fusedMap1152_checked : acceptsGraphIso
    (fused (graph core1152) (root 10) 2 2) DegreeTwoThreeSpectrum6688.graph fusedMap1152=true := by decide +kernel
theorem certified1152 : Certified (graph core1152) (root 10) 2 2 :=
  of_native_maps core1152 DegreeOneMiddleResidualSpectrum2227.graph DegreeTwoThreeSpectrum6688.graph
    sourceMap1152 fusedMap1152 sourceMap1152_checked fusedMap1152_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1152
#print axioms sourceMap1152_checked
#print axioms fusedMap1152_checked
#print axioms certified1152
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

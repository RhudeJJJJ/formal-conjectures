/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1085 : Family 10 := level10.get ⟨1127,by decide⟩
def sourceMap1085 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1085 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1085_checked : acceptsGraphIso
    (source (graph core1085) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2065.graph sourceMap1085=true := by decide +kernel
theorem fusedMap1085_checked : acceptsGraphIso
    (fused (graph core1085) (root 10) 2 2) DegreeTwoThreeSpectrum6240.graph fusedMap1085=true := by decide +kernel
theorem certified1085 : Certified (graph core1085) (root 10) 2 2 :=
  of_native_maps core1085 DegreeOneMiddleResidualSpectrum2065.graph DegreeTwoThreeSpectrum6240.graph
    sourceMap1085 fusedMap1085 sourceMap1085_checked fusedMap1085_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1085
#print axioms sourceMap1085_checked
#print axioms fusedMap1085_checked
#print axioms certified1085
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1054 : Family 10 := level10.get ⟨1046,by decide⟩
def sourceMap1054 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1054 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1054_checked : acceptsGraphIso
    (source (graph core1054) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2002.graph sourceMap1054=true := by decide +kernel
theorem fusedMap1054_checked : acceptsGraphIso
    (fused (graph core1054) (root 10) 2 2) DegreeTwoThreeSpectrum6076.graph fusedMap1054=true := by decide +kernel
theorem certified1054 : Certified (graph core1054) (root 10) 2 2 :=
  of_native_maps core1054 DegreeOneMiddleResidualSpectrum2002.graph DegreeTwoThreeSpectrum6076.graph
    sourceMap1054 fusedMap1054 sourceMap1054_checked fusedMap1054_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1054
#print axioms sourceMap1054_checked
#print axioms fusedMap1054_checked
#print axioms certified1054
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

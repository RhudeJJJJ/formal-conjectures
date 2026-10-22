/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1086 : Family 10 := level10.get ⟨1129,by decide⟩
def sourceMap1086 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1086 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1086_checked : acceptsGraphIso
    (source (graph core1086) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2067.graph sourceMap1086=true := by decide +kernel
theorem fusedMap1086_checked : acceptsGraphIso
    (fused (graph core1086) (root 10) 2 2) DegreeTwoThreeSpectrum6246.graph fusedMap1086=true := by decide +kernel
theorem certified1086 : Certified (graph core1086) (root 10) 2 2 :=
  of_native_maps core1086 DegreeOneMiddleResidualSpectrum2067.graph DegreeTwoThreeSpectrum6246.graph
    sourceMap1086 fusedMap1086 sourceMap1086_checked fusedMap1086_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1086
#print axioms sourceMap1086_checked
#print axioms fusedMap1086_checked
#print axioms certified1086
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

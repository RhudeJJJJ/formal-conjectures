/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1034 : Family 10 := level10.get ⟨1008,by decide⟩
def sourceMap1034 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1034 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1034_checked : acceptsGraphIso
    (source (graph core1034) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1969.graph sourceMap1034=true := by decide +kernel
theorem fusedMap1034_checked : acceptsGraphIso
    (fused (graph core1034) (root 10) 2 2) DegreeTwoThreeSpectrum5996.graph fusedMap1034=true := by decide +kernel
theorem certified1034 : Certified (graph core1034) (root 10) 2 2 :=
  of_native_maps core1034 DegreeOneMiddleResidualSpectrum1969.graph DegreeTwoThreeSpectrum5996.graph
    sourceMap1034 fusedMap1034 sourceMap1034_checked fusedMap1034_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1034
#print axioms sourceMap1034_checked
#print axioms fusedMap1034_checked
#print axioms certified1034
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

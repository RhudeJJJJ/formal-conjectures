/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1041 : Family 10 := level10.get ⟨1020,by decide⟩
def sourceMap1041 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1041 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1041_checked : acceptsGraphIso
    (source (graph core1041) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1980.graph sourceMap1041=true := by decide +kernel
theorem fusedMap1041_checked : acceptsGraphIso
    (fused (graph core1041) (root 10) 2 2) DegreeTwoThreeSpectrum6024.graph fusedMap1041=true := by decide +kernel
theorem certified1041 : Certified (graph core1041) (root 10) 2 2 :=
  of_native_maps core1041 DegreeOneMiddleResidualSpectrum1980.graph DegreeTwoThreeSpectrum6024.graph
    sourceMap1041 fusedMap1041 sourceMap1041_checked fusedMap1041_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1041
#print axioms sourceMap1041_checked
#print axioms fusedMap1041_checked
#print axioms certified1041
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

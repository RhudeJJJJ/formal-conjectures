/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1050 : Family 10 := level10.get ⟨1038,by decide⟩
def sourceMap1050 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1050 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1050_checked : acceptsGraphIso
    (source (graph core1050) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1995.graph sourceMap1050=true := by decide +kernel
theorem fusedMap1050_checked : acceptsGraphIso
    (fused (graph core1050) (root 10) 2 2) DegreeTwoThreeSpectrum6059.graph fusedMap1050=true := by decide +kernel
theorem certified1050 : Certified (graph core1050) (root 10) 2 2 :=
  of_native_maps core1050 DegreeOneMiddleResidualSpectrum1995.graph DegreeTwoThreeSpectrum6059.graph
    sourceMap1050 fusedMap1050 sourceMap1050_checked fusedMap1050_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1050
#print axioms sourceMap1050_checked
#print axioms fusedMap1050_checked
#print axioms certified1050
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

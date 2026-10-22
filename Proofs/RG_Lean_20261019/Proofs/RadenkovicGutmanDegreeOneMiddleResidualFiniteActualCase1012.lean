/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1012 : Family 10 := level10.get ⟨928,by decide⟩
def sourceMap1012 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1012 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1012_checked : acceptsGraphIso
    (source (graph core1012) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2315.graph sourceMap1012=true := by decide +kernel
theorem fusedMap1012_checked : acceptsGraphIso
    (fused (graph core1012) (root 10) 2 2) DegreeTwoThreeSpectrum5822.graph fusedMap1012=true := by decide +kernel
theorem certified1012 : Certified (graph core1012) (root 10) 2 2 :=
  of_native_maps core1012 DegreeOneMiddleResidualSpectrum2315.graph DegreeTwoThreeSpectrum5822.graph
    sourceMap1012 fusedMap1012 sourceMap1012_checked fusedMap1012_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1012
#print axioms sourceMap1012_checked
#print axioms fusedMap1012_checked
#print axioms certified1012
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

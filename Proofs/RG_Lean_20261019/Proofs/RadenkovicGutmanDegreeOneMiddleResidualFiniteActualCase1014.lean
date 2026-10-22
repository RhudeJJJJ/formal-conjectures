/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1014 : Family 10 := level10.get ⟨931,by decide⟩
def sourceMap1014 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1014 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1014_checked : acceptsGraphIso
    (source (graph core1014) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2317.graph sourceMap1014=true := by decide +kernel
theorem fusedMap1014_checked : acceptsGraphIso
    (fused (graph core1014) (root 10) 2 2) DegreeTwoThreeSpectrum5826.graph fusedMap1014=true := by decide +kernel
theorem certified1014 : Certified (graph core1014) (root 10) 2 2 :=
  of_native_maps core1014 DegreeOneMiddleResidualSpectrum2317.graph DegreeTwoThreeSpectrum5826.graph
    sourceMap1014 fusedMap1014 sourceMap1014_checked fusedMap1014_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1014
#print axioms sourceMap1014_checked
#print axioms fusedMap1014_checked
#print axioms certified1014
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases

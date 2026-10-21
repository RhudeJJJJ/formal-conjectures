/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1886 : Family 10 := level10.get ⟨153,by decide⟩
def sourceMap1886 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1886 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1886_checked : acceptsGraphIso
    (source (graph core1886) (root 10) 0 0) DegreeOneSmallSpectrum1182.graph sourceMap1886=true := by decide +kernel
theorem fusedMap1886_checked : acceptsGraphIso
    (fused (graph core1886) (root 10) 0 0) DegreeOneSmallSpectrum964.graph fusedMap1886=true := by decide +kernel
theorem certified1886 : Certified (graph core1886) (root 10) 0 0 :=
  of_native_maps core1886 DegreeOneSmallSpectrum1182.graph DegreeOneSmallSpectrum964.graph
    sourceMap1886 fusedMap1886 sourceMap1886_checked fusedMap1886_checked
    DegreeOneSmallComparisons.comparison1886
#print axioms sourceMap1886_checked
#print axioms fusedMap1886_checked
#print axioms certified1886
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

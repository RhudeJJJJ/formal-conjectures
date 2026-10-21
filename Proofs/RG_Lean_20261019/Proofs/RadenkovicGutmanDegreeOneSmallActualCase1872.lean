/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1872 : Family 10 := level10.get ⟨133,by decide⟩
def sourceMap1872 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1872 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1872_checked : acceptsGraphIso
    (source (graph core1872) (root 10) 0 0) DegreeOneSmallSpectrum1245.graph sourceMap1872=true := by decide +kernel
theorem fusedMap1872_checked : acceptsGraphIso
    (fused (graph core1872) (root 10) 0 0) DegreeOneSmallSpectrum960.graph fusedMap1872=true := by decide +kernel
theorem certified1872 : Certified (graph core1872) (root 10) 0 0 :=
  of_native_maps core1872 DegreeOneSmallSpectrum1245.graph DegreeOneSmallSpectrum960.graph
    sourceMap1872 fusedMap1872 sourceMap1872_checked fusedMap1872_checked
    DegreeOneSmallComparisons.comparison1872
#print axioms sourceMap1872_checked
#print axioms fusedMap1872_checked
#print axioms certified1872
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

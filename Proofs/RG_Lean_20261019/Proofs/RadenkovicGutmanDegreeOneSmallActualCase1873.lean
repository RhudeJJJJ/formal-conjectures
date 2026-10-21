/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1873 : Family 10 := level10.get ⟨134,by decide⟩
def sourceMap1873 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1873 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1873_checked : acceptsGraphIso
    (source (graph core1873) (root 10) 0 0) DegreeOneSmallSpectrum1180.graph sourceMap1873=true := by decide +kernel
theorem fusedMap1873_checked : acceptsGraphIso
    (fused (graph core1873) (root 10) 0 0) DegreeOneSmallSpectrum959.graph fusedMap1873=true := by decide +kernel
theorem certified1873 : Certified (graph core1873) (root 10) 0 0 :=
  of_native_maps core1873 DegreeOneSmallSpectrum1180.graph DegreeOneSmallSpectrum959.graph
    sourceMap1873 fusedMap1873 sourceMap1873_checked fusedMap1873_checked
    DegreeOneSmallComparisons.comparison1873
#print axioms sourceMap1873_checked
#print axioms fusedMap1873_checked
#print axioms certified1873
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

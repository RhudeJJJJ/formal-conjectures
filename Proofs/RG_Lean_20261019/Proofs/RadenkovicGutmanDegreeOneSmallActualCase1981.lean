/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1981 : Family 10 := level10.get ⟨305,by decide⟩
def sourceMap1981 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1981 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1981_checked : acceptsGraphIso
    (source (graph core1981) (root 10) 0 0) DegreeOneSmallSpectrum1259.graph sourceMap1981=true := by decide +kernel
theorem fusedMap1981_checked : acceptsGraphIso
    (fused (graph core1981) (root 10) 0 0) DegreeOneSmallSpectrum1358.graph fusedMap1981=true := by decide +kernel
theorem certified1981 : Certified (graph core1981) (root 10) 0 0 :=
  of_native_maps core1981 DegreeOneSmallSpectrum1259.graph DegreeOneSmallSpectrum1358.graph
    sourceMap1981 fusedMap1981 sourceMap1981_checked fusedMap1981_checked
    DegreeOneSmallComparisons.comparison1981
#print axioms sourceMap1981_checked
#print axioms fusedMap1981_checked
#print axioms certified1981
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

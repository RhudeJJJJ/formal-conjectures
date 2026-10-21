/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1984 : Family 10 := level10.get ⟨309,by decide⟩
def sourceMap1984 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1984 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1984_checked : acceptsGraphIso
    (source (graph core1984) (root 10) 0 0) DegreeOneSmallSpectrum1261.graph sourceMap1984=true := by decide +kernel
theorem fusedMap1984_checked : acceptsGraphIso
    (fused (graph core1984) (root 10) 0 0) DegreeOneSmallSpectrum1370.graph fusedMap1984=true := by decide +kernel
theorem certified1984 : Certified (graph core1984) (root 10) 0 0 :=
  of_native_maps core1984 DegreeOneSmallSpectrum1261.graph DegreeOneSmallSpectrum1370.graph
    sourceMap1984 fusedMap1984 sourceMap1984_checked fusedMap1984_checked
    DegreeOneSmallComparisons.comparison1984
#print axioms sourceMap1984_checked
#print axioms fusedMap1984_checked
#print axioms certified1984
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

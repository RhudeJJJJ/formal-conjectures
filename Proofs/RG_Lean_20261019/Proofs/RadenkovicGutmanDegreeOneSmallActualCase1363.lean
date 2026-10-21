/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1363 : Family 9 := level9.get ⟨113,by decide⟩
def sourceMap1363 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1363 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1363_checked : acceptsGraphIso
    (source (graph core1363) (root 9) 0 0) DegreeOneSmallSpectrum459.graph sourceMap1363=true := by decide +kernel
theorem fusedMap1363_checked : acceptsGraphIso
    (fused (graph core1363) (root 9) 0 0) DegreeOneSmallSpectrum586.graph fusedMap1363=true := by decide +kernel
theorem certified1363 : Certified (graph core1363) (root 9) 0 0 :=
  of_native_maps core1363 DegreeOneSmallSpectrum459.graph DegreeOneSmallSpectrum586.graph
    sourceMap1363 fusedMap1363 sourceMap1363_checked fusedMap1363_checked
    DegreeOneSmallComparisons.comparison1363
#print axioms sourceMap1363_checked
#print axioms fusedMap1363_checked
#print axioms certified1363
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1373 : Family 9 := level9.get ⟨120,by decide⟩
def sourceMap1373 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,7,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1373 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1373_checked : acceptsGraphIso
    (source (graph core1373) (root 9) 0 0) DegreeOneSmallSpectrum430.graph sourceMap1373=true := by decide +kernel
theorem fusedMap1373_checked : acceptsGraphIso
    (fused (graph core1373) (root 9) 0 0) DegreeOneSmallSpectrum575.graph fusedMap1373=true := by decide +kernel
theorem certified1373 : Certified (graph core1373) (root 9) 0 0 :=
  of_native_maps core1373 DegreeOneSmallSpectrum430.graph DegreeOneSmallSpectrum575.graph
    sourceMap1373 fusedMap1373 sourceMap1373_checked fusedMap1373_checked
    DegreeOneSmallComparisons.comparison1373
#print axioms sourceMap1373_checked
#print axioms fusedMap1373_checked
#print axioms certified1373
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

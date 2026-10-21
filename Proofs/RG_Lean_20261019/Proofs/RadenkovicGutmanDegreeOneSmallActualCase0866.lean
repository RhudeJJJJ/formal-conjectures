/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0866 : Family 8 := level8.get ⟨41,by decide⟩
def sourceMap0866 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0866 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0866_checked : acceptsGraphIso
    (source (graph core0866) (root 8) 1 1) DegreeOneSmallSpectrum1151.graph sourceMap0866=true := by decide +kernel
theorem fusedMap0866_checked : acceptsGraphIso
    (fused (graph core0866) (root 8) 1 1) DegreeOneSmallSpectrum873.graph fusedMap0866=true := by decide +kernel
theorem certified0866 : Certified (graph core0866) (root 8) 1 1 :=
  of_native_maps core0866 DegreeOneSmallSpectrum1151.graph DegreeOneSmallSpectrum873.graph
    sourceMap0866 fusedMap0866 sourceMap0866_checked fusedMap0866_checked
    DegreeOneSmallComparisons.comparison0866
#print axioms sourceMap0866_checked
#print axioms fusedMap0866_checked
#print axioms certified0866
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

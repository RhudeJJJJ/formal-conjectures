/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0389 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0389 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0389 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0389_checked : acceptsGraphIso
    (source (graph core0389) (root 6) 1 1) DegreeOneSmallSpectrum242.graph sourceMap0389=true := by decide +kernel
theorem fusedMap0389_checked : acceptsGraphIso
    (fused (graph core0389) (root 6) 1 1) SmallGeFourSpectrum037.graph fusedMap0389=true := by decide +kernel
theorem certified0389 : Certified (graph core0389) (root 6) 1 1 :=
  of_native_maps core0389 DegreeOneSmallSpectrum242.graph SmallGeFourSpectrum037.graph
    sourceMap0389 fusedMap0389 sourceMap0389_checked fusedMap0389_checked
    DegreeOneSmallComparisons.comparison0389
#print axioms sourceMap0389_checked
#print axioms fusedMap0389_checked
#print axioms certified0389
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

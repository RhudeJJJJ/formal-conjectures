/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0910 : Family 8 := level8.get ⟨58,by decide⟩
def sourceMap0910 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0910 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0910_checked : acceptsGraphIso
    (source (graph core0910) (root 8) 1 1) DegreeOneSmallSpectrum1334.graph sourceMap0910=true := by decide +kernel
theorem fusedMap0910_checked : acceptsGraphIso
    (fused (graph core0910) (root 8) 1 1) DegreeOneSmallSpectrum917.graph fusedMap0910=true := by decide +kernel
theorem certified0910 : Certified (graph core0910) (root 8) 1 1 :=
  of_native_maps core0910 DegreeOneSmallSpectrum1334.graph DegreeOneSmallSpectrum917.graph
    sourceMap0910 fusedMap0910 sourceMap0910_checked fusedMap0910_checked
    DegreeOneSmallComparisons.comparison0910
#print axioms sourceMap0910_checked
#print axioms fusedMap0910_checked
#print axioms certified0910
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

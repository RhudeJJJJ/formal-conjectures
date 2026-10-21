/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0955 : Family 8 := level8.get ⟨76,by decide⟩
def sourceMap0955 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0955 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0955_checked : acceptsGraphIso
    (source (graph core0955) (root 8) 0 0) DegreeOneSmallSpectrum300.graph sourceMap0955=true := by decide +kernel
theorem fusedMap0955_checked : acceptsGraphIso
    (fused (graph core0955) (root 8) 0 0) DegreeOneSmallSpectrum224.graph fusedMap0955=true := by decide +kernel
theorem certified0955 : Certified (graph core0955) (root 8) 0 0 :=
  of_native_maps core0955 DegreeOneSmallSpectrum300.graph DegreeOneSmallSpectrum224.graph
    sourceMap0955 fusedMap0955 sourceMap0955_checked fusedMap0955_checked
    DegreeOneSmallComparisons.comparison0955
#print axioms sourceMap0955_checked
#print axioms fusedMap0955_checked
#print axioms certified0955
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0979 : Family 8 := level8.get ⟨87,by decide⟩
def sourceMap0979 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,8,9,10,5,6,7,3,4] (sourceLabel 8 0 0 v)
def fusedMap0979 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0979_checked : acceptsGraphIso
    (source (graph core0979) (root 8) 0 0) SmallGeFourSpectrum049.graph sourceMap0979=true := by decide +kernel
theorem fusedMap0979_checked : acceptsGraphIso
    (fused (graph core0979) (root 8) 0 0) SmallGeFourSpectrum039.graph fusedMap0979=true := by decide +kernel
theorem certified0979 : Certified (graph core0979) (root 8) 0 0 :=
  of_native_maps core0979 SmallGeFourSpectrum049.graph SmallGeFourSpectrum039.graph
    sourceMap0979 fusedMap0979 sourceMap0979_checked fusedMap0979_checked
    DegreeOneSmallComparisons.comparison0979
#print axioms sourceMap0979_checked
#print axioms fusedMap0979_checked
#print axioms certified0979
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

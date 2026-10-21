/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0439 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0439 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0439 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0439_checked : acceptsGraphIso
    (source (graph core0439) (root 6) 0 1) SmallGeFourSpectrum029.graph sourceMap0439=true := by decide +kernel
theorem fusedMap0439_checked : acceptsGraphIso
    (fused (graph core0439) (root 6) 0 1) SmallGeFourSpectrum015.graph fusedMap0439=true := by decide +kernel
theorem certified0439 : Certified (graph core0439) (root 6) 0 1 :=
  of_native_maps core0439 SmallGeFourSpectrum029.graph SmallGeFourSpectrum015.graph
    sourceMap0439 fusedMap0439 sourceMap0439_checked fusedMap0439_checked
    DegreeOneSmallComparisons.comparison0439
#print axioms sourceMap0439_checked
#print axioms fusedMap0439_checked
#print axioms certified0439
def sourceMap0439swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0439swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0439swap_checked : acceptsGraphIso
    (source (graph core0439) (root 6) 1 0) SmallGeFourSpectrum029.graph sourceMap0439swap=true := by decide +kernel
theorem fusedMap0439swap_checked : acceptsGraphIso
    (fused (graph core0439) (root 6) 1 0) SmallGeFourSpectrum015.graph fusedMap0439swap=true := by decide +kernel
theorem certified0439swap : Certified (graph core0439) (root 6) 1 0 :=
  of_native_maps core0439 SmallGeFourSpectrum029.graph SmallGeFourSpectrum015.graph
    sourceMap0439swap fusedMap0439swap sourceMap0439swap_checked fusedMap0439swap_checked
    DegreeOneSmallComparisons.comparison0439
#print axioms sourceMap0439swap_checked
#print axioms fusedMap0439swap_checked
#print axioms certified0439swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

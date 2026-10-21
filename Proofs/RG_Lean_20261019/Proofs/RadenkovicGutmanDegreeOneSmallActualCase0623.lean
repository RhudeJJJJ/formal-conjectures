/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0623 : Family 7 := level7.get ⟨42,by decide⟩
def sourceMap0623 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0623 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0623_checked : acceptsGraphIso
    (source (graph core0623) (root 7) 0 2) SmallGeFourSpectrum103.graph sourceMap0623=true := by decide +kernel
theorem fusedMap0623_checked : acceptsGraphIso
    (fused (graph core0623) (root 7) 0 2) SmallGeFourSpectrum104.graph fusedMap0623=true := by decide +kernel
theorem certified0623 : Certified (graph core0623) (root 7) 0 2 :=
  of_native_maps core0623 SmallGeFourSpectrum103.graph SmallGeFourSpectrum104.graph
    sourceMap0623 fusedMap0623 sourceMap0623_checked fusedMap0623_checked
    DegreeOneSmallComparisons.comparison0623
#print axioms sourceMap0623_checked
#print axioms fusedMap0623_checked
#print axioms certified0623
def sourceMap0623swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0623swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0623swap_checked : acceptsGraphIso
    (source (graph core0623) (root 7) 2 0) SmallGeFourSpectrum103.graph sourceMap0623swap=true := by decide +kernel
theorem fusedMap0623swap_checked : acceptsGraphIso
    (fused (graph core0623) (root 7) 2 0) SmallGeFourSpectrum104.graph fusedMap0623swap=true := by decide +kernel
theorem certified0623swap : Certified (graph core0623) (root 7) 2 0 :=
  of_native_maps core0623 SmallGeFourSpectrum103.graph SmallGeFourSpectrum104.graph
    sourceMap0623swap fusedMap0623swap sourceMap0623swap_checked fusedMap0623swap_checked
    DegreeOneSmallComparisons.comparison0623
#print axioms sourceMap0623swap_checked
#print axioms fusedMap0623swap_checked
#print axioms certified0623swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0625 : Family 7 := level7.get ⟨42,by decide⟩
def sourceMap0625 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0625 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0625_checked : acceptsGraphIso
    (source (graph core0625) (root 7) 1 1) SmallGeFourSpectrum176.graph sourceMap0625=true := by decide +kernel
theorem fusedMap0625_checked : acceptsGraphIso
    (fused (graph core0625) (root 7) 1 1) SmallGeFourSpectrum104.graph fusedMap0625=true := by decide +kernel
theorem certified0625 : Certified (graph core0625) (root 7) 1 1 :=
  of_native_maps core0625 SmallGeFourSpectrum176.graph SmallGeFourSpectrum104.graph
    sourceMap0625 fusedMap0625 sourceMap0625_checked fusedMap0625_checked
    DegreeOneSmallComparisons.comparison0625
#print axioms sourceMap0625_checked
#print axioms fusedMap0625_checked
#print axioms certified0625
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases

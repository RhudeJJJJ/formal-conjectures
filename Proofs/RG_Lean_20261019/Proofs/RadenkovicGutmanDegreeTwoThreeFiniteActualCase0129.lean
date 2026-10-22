/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0129 : Family 8 := level8.get ⟨198,by decide⟩
def sourceMap0129 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0129 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0129_checked : acceptsGraphIso
    (source (graph core0129) (root 8) 0 0) DegreeTwoThreeSpectrum319.graph sourceMap0129=true := by decide +kernel
theorem fusedMap0129_checked : acceptsGraphIso
    (fused (graph core0129) (root 8) 0 0) DegreeOneSmallSpectrum248.graph fusedMap0129=true := by decide +kernel
theorem certified0129 : Certified (graph core0129) (root 8) 0 0 :=
  of_native_maps core0129 DegreeTwoThreeSpectrum319.graph DegreeOneSmallSpectrum248.graph
    sourceMap0129 fusedMap0129 sourceMap0129_checked fusedMap0129_checked
    DegreeTwoThreeFiniteComparisons.comparison0129
#print axioms sourceMap0129_checked
#print axioms fusedMap0129_checked
#print axioms certified0129
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

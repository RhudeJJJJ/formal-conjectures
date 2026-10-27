/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4722 : Family 10 := level10.get ⟨937,by decide⟩
def sourceMap4722 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4722 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4722_checked : acceptsGraphIso
    (source (graph core4722) (root 10) 2 2) DegreeTwoThreeSpectrum7547.graph sourceMap4722=true := by decide +kernel
theorem fusedMap4722_checked : acceptsGraphIso
    (fused (graph core4722) (root 10) 2 2) DegreeTwoThreeSpectrum5832.graph fusedMap4722=true := by decide +kernel
theorem certified4722 : Certified (graph core4722) (root 10) 2 2 :=
  of_native_maps core4722 DegreeTwoThreeSpectrum7547.graph DegreeTwoThreeSpectrum5832.graph
    sourceMap4722 fusedMap4722 sourceMap4722_checked fusedMap4722_checked
    DegreeTwoThreeFiniteComparisons.comparison4722
#print axioms sourceMap4722_checked
#print axioms fusedMap4722_checked
#print axioms certified4722
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

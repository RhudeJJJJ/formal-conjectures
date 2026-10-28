/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4891 : Family 10 := level10.get ⟨1350,by decide⟩
def sourceMap4891 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4891 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4891_checked : acceptsGraphIso
    (source (graph core4891) (root 10) 2 2) DegreeTwoThreeSpectrum7434.graph sourceMap4891=true := by decide +kernel
theorem fusedMap4891_checked : acceptsGraphIso
    (fused (graph core4891) (root 10) 2 2) DegreeTwoThreeSpectrum6682.graph fusedMap4891=true := by decide +kernel
theorem certified4891 : Certified (graph core4891) (root 10) 2 2 :=
  of_native_maps core4891 DegreeTwoThreeSpectrum7434.graph DegreeTwoThreeSpectrum6682.graph
    sourceMap4891 fusedMap4891 sourceMap4891_checked fusedMap4891_checked
    DegreeTwoThreeFiniteComparisons.comparison4891
#print axioms sourceMap4891_checked
#print axioms fusedMap4891_checked
#print axioms certified4891
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

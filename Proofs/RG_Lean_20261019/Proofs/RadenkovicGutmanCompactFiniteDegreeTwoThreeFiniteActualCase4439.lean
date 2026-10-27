/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4439 : Family 10 := level10.get ⟨50,by decide⟩
def sourceMap4439 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,10,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4439 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 2 2 v)
theorem sourceMap4439_checked : acceptsGraphIso
    (source (graph core4439) (root 10) 2 2) DegreeTwoThreeSpectrum5656.graph sourceMap4439=true := by decide +kernel
theorem fusedMap4439_checked : acceptsGraphIso
    (fused (graph core4439) (root 10) 2 2) DegreeTwoThreeSpectrum5132.graph fusedMap4439=true := by decide +kernel
theorem certified4439 : Certified (graph core4439) (root 10) 2 2 :=
  of_native_maps core4439 DegreeTwoThreeSpectrum5656.graph DegreeTwoThreeSpectrum5132.graph
    sourceMap4439 fusedMap4439 sourceMap4439_checked fusedMap4439_checked
    DegreeTwoThreeFiniteComparisons.comparison4439
#print axioms sourceMap4439_checked
#print axioms fusedMap4439_checked
#print axioms certified4439
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

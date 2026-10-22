/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5380 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap5380 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 4 4 v)
def fusedMap5380 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 4 4 v)
theorem sourceMap5380_checked : acceptsGraphIso
    (source (graph core5380) (root 5) 4 4) DegreeTwoThreeSpectrum4662.graph sourceMap5380=true := by decide +kernel
theorem fusedMap5380_checked : acceptsGraphIso
    (fused (graph core5380) (root 5) 4 4) DegreeTwoThreeSpectrum3902.graph fusedMap5380=true := by decide +kernel
theorem certified5380 : Certified (graph core5380) (root 5) 4 4 :=
  of_native_maps core5380 DegreeTwoThreeSpectrum4662.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap5380 fusedMap5380 sourceMap5380_checked fusedMap5380_checked
    DegreeTwoThreeFiniteComparisons.comparison5380
#print axioms sourceMap5380_checked
#print axioms fusedMap5380_checked
#print axioms certified5380
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases

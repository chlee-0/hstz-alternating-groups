import HSTZ.TauCetiFinite.Degrees.D14.Data00
import HSTZ.TauCetiFinite.Degrees.D14.Data01
import HSTZ.TauCetiFinite.Degrees.D14.Data02
import HSTZ.TauCetiFinite.Degrees.D14.Data03
import HSTZ.TauCetiFinite.Degrees.D14.Data04
import HSTZ.TauCetiFinite.Degrees.D14.Data05
import HSTZ.TauCetiFinite.Degrees.D14.Data06
import HSTZ.TauCetiFinite.Degrees.D14.Data07
import HSTZ.TauCetiFinite.Degrees.D14.Data08
import HSTZ.TauCetiFinite.Degrees.D14.Data09
import HSTZ.TauCetiFinite.Degrees.D14.Data10
import HSTZ.TauCetiFinite.Degrees.D14.Data11
import HSTZ.TauCetiFinite.Degrees.D14.Data12
import HSTZ.TauCetiFinite.Degrees.D14.Data13
import HSTZ.TauCetiFinite.Degrees.D14.Data14
import HSTZ.TauCetiFinite.Degrees.D14.Data15
import HSTZ.TauCetiFinite.Degrees.D14.Data16
import HSTZ.TauCetiFinite.Degrees.D14.Data17
import HSTZ.TauCetiFinite.Degrees.D14.Data18
import HSTZ.TauCetiFinite.Degrees.D14.Data19
import HSTZ.TauCetiFinite.Degrees.D14.Data20
import HSTZ.TauCetiFinite.Degrees.D14.Data21

/-! Part of the degree-14 finite character certificate (`HSTZ.TauCetiFinite.D14`),
split into separate modules to bound memory use. -/
namespace HSTZ.TauCetiFinite.D14
open HSTZ.MurnaghanNakayama

def blockGroup0 : ℕ → Array IndexedEntry
  | 0 => block0
  | 1 => block1
  | 2 => block2
  | 3 => block3
  | 4 => block4
  | 5 => block5
  | 6 => block6
  | 7 => block7
  | 8 => block8
  | 9 => block9
  | 10 => block10
  | 11 => block11
  | 12 => block12
  | 13 => block13
  | 14 => block14
  | 15 => block15
  | _ => #[]

def blockGroup1 : ℕ → Array IndexedEntry
  | 0 => block16
  | 1 => block17
  | 2 => block18
  | 3 => block19
  | 4 => block20
  | 5 => block21
  | 6 => block22
  | 7 => block23
  | 8 => block24
  | 9 => block25
  | 10 => block26
  | 11 => block27
  | 12 => block28
  | 13 => block29
  | 14 => block30
  | 15 => block31
  | _ => #[]

def blockGroup2 : ℕ → Array IndexedEntry
  | 0 => block32
  | 1 => block33
  | 2 => block34
  | 3 => block35
  | 4 => block36
  | 5 => block37
  | 6 => block38
  | 7 => block39
  | 8 => block40
  | 9 => block41
  | 10 => block42
  | 11 => block43
  | 12 => block44
  | 13 => block45
  | 14 => block46
  | 15 => block47
  | _ => #[]

def blockGroup3 : ℕ → Array IndexedEntry
  | 0 => block48
  | 1 => block49
  | 2 => block50
  | 3 => block51
  | 4 => block52
  | 5 => block53
  | 6 => block54
  | 7 => block55
  | 8 => block56
  | 9 => block57
  | 10 => block58
  | 11 => block59
  | 12 => block60
  | 13 => block61
  | 14 => block62
  | 15 => block63
  | _ => #[]

def blockGroup4 : ℕ → Array IndexedEntry
  | 0 => block64
  | 1 => block65
  | 2 => block66
  | 3 => block67
  | 4 => block68
  | 5 => block69
  | 6 => block70
  | 7 => block71
  | 8 => block72
  | 9 => block73
  | 10 => block74
  | 11 => block75
  | 12 => block76
  | 13 => block77
  | 14 => block78
  | 15 => block79
  | _ => #[]

def blockGroup5 : ℕ → Array IndexedEntry
  | 0 => block80
  | 1 => block81
  | 2 => block82
  | 3 => block83
  | 4 => block84
  | 5 => block85
  | 6 => block86
  | 7 => block87
  | 8 => block88
  | 9 => block89
  | 10 => block90
  | 11 => block91
  | 12 => block92
  | 13 => block93
  | 14 => block94
  | 15 => block95
  | _ => #[]

def blockGroup6 : ℕ → Array IndexedEntry
  | 0 => block96
  | 1 => block97
  | 2 => block98
  | 3 => block99
  | 4 => block100
  | 5 => block101
  | 6 => block102
  | 7 => block103
  | 8 => block104
  | 9 => block105
  | 10 => block106
  | 11 => block107
  | 12 => block108
  | 13 => block109
  | 14 => block110
  | 15 => block111
  | _ => #[]

def blockGroup7 : ℕ → Array IndexedEntry
  | 0 => block112
  | 1 => block113
  | 2 => block114
  | 3 => block115
  | 4 => block116
  | 5 => block117
  | 6 => block118
  | 7 => block119
  | 8 => block120
  | 9 => block121
  | 10 => block122
  | 11 => block123
  | 12 => block124
  | 13 => block125
  | 14 => block126
  | 15 => block127
  | _ => #[]

def blockGroup8 : ℕ → Array IndexedEntry
  | 0 => block128
  | 1 => block129
  | 2 => block130
  | 3 => block131
  | 4 => block132
  | 5 => block133
  | 6 => block134
  | 7 => block135
  | 8 => block136
  | 9 => block137
  | 10 => block138
  | 11 => block139
  | 12 => block140
  | 13 => block141
  | 14 => block142
  | 15 => block143
  | _ => #[]

def blockGroup9 : ℕ → Array IndexedEntry
  | 0 => block144
  | 1 => block145
  | 2 => block146
  | 3 => block147
  | 4 => block148
  | 5 => block149
  | 6 => block150
  | 7 => block151
  | 8 => block152
  | 9 => block153
  | 10 => block154
  | 11 => block155
  | 12 => block156
  | 13 => block157
  | 14 => block158
  | 15 => block159
  | _ => #[]

def blockGroup10 : ℕ → Array IndexedEntry
  | 0 => block160
  | 1 => block161
  | 2 => block162
  | 3 => block163
  | 4 => block164
  | 5 => block165
  | 6 => block166
  | 7 => block167
  | 8 => block168
  | 9 => block169
  | 10 => block170
  | 11 => block171
  | 12 => block172
  | 13 => block173
  | 14 => block174
  | 15 => block175
  | _ => #[]

def blockGroup11 : ℕ → Array IndexedEntry
  | 0 => block176
  | 1 => block177
  | 2 => block178
  | 3 => block179
  | 4 => block180
  | 5 => block181
  | 6 => block182
  | 7 => block183
  | 8 => block184
  | 9 => block185
  | 10 => block186
  | 11 => block187
  | 12 => block188
  | 13 => block189
  | 14 => block190
  | 15 => block191
  | _ => #[]

def blockGroup12 : ℕ → Array IndexedEntry
  | 0 => block192
  | 1 => block193
  | 2 => block194
  | 3 => block195
  | 4 => block196
  | 5 => block197
  | 6 => block198
  | 7 => block199
  | 8 => block200
  | 9 => block201
  | 10 => block202
  | 11 => block203
  | 12 => block204
  | 13 => block205
  | 14 => block206
  | 15 => block207
  | _ => #[]

def blockGroup13 : ℕ → Array IndexedEntry
  | 0 => block208
  | 1 => block209
  | 2 => block210
  | 3 => block211
  | 4 => block212
  | 5 => block213
  | 6 => block214
  | 7 => block215
  | 8 => block216
  | 9 => block217
  | 10 => block218
  | 11 => block219
  | 12 => block220
  | 13 => block221
  | 14 => block222
  | 15 => block223
  | _ => #[]

def blockGroup14 : ℕ → Array IndexedEntry
  | 0 => block224
  | 1 => block225
  | 2 => block226
  | 3 => block227
  | 4 => block228
  | 5 => block229
  | 6 => block230
  | 7 => block231
  | 8 => block232
  | 9 => block233
  | 10 => block234
  | 11 => block235
  | 12 => block236
  | 13 => block237
  | 14 => block238
  | 15 => block239
  | _ => #[]

def blockGroup15 : ℕ → Array IndexedEntry
  | 0 => block240
  | 1 => block241
  | 2 => block242
  | 3 => block243
  | 4 => block244
  | 5 => block245
  | 6 => block246
  | 7 => block247
  | 8 => block248
  | 9 => block249
  | 10 => block250
  | 11 => block251
  | 12 => block252
  | 13 => block253
  | 14 => block254
  | 15 => block255
  | _ => #[]

def blockGroup16 : ℕ → Array IndexedEntry
  | 0 => block256
  | 1 => block257
  | 2 => block258
  | 3 => block259
  | 4 => block260
  | 5 => block261
  | 6 => block262
  | 7 => block263
  | 8 => block264
  | 9 => block265
  | 10 => block266
  | 11 => block267
  | 12 => block268
  | 13 => block269
  | 14 => block270
  | 15 => block271
  | _ => #[]

def blockGroup17 : ℕ → Array IndexedEntry
  | 0 => block272
  | 1 => block273
  | 2 => block274
  | 3 => block275
  | 4 => block276
  | 5 => block277
  | 6 => block278
  | 7 => block279
  | 8 => block280
  | 9 => block281
  | 10 => block282
  | 11 => block283
  | 12 => block284
  | 13 => block285
  | 14 => block286
  | 15 => block287
  | _ => #[]

def blockGroup18 : ℕ → Array IndexedEntry
  | 0 => block288
  | 1 => block289
  | 2 => block290
  | 3 => block291
  | 4 => block292
  | 5 => block293
  | 6 => block294
  | 7 => block295
  | 8 => block296
  | 9 => block297
  | 10 => block298
  | 11 => block299
  | 12 => block300
  | 13 => block301
  | 14 => block302
  | 15 => block303
  | _ => #[]

def blockGroup19 : ℕ → Array IndexedEntry
  | 0 => block304
  | 1 => block305
  | 2 => block306
  | 3 => block307
  | 4 => block308
  | 5 => block309
  | 6 => block310
  | 7 => block311
  | 8 => block312
  | 9 => block313
  | 10 => block314
  | 11 => block315
  | 12 => block316
  | 13 => block317
  | 14 => block318
  | 15 => block319
  | _ => #[]

def blockGroup20 : ℕ → Array IndexedEntry
  | 0 => block320
  | 1 => block321
  | 2 => block322
  | 3 => block323
  | 4 => block324
  | 5 => block325
  | 6 => block326
  | 7 => block327
  | 8 => block328
  | 9 => block329
  | 10 => block330
  | 11 => block331
  | 12 => block332
  | 13 => block333
  | 14 => block334
  | 15 => block335
  | _ => #[]

def blockGroup21 : ℕ → Array IndexedEntry
  | 0 => block336
  | 1 => block337
  | 2 => block338
  | 3 => block339
  | 4 => block340
  | 5 => block341
  | 6 => block342
  | 7 => block343
  | 8 => block344
  | 9 => block345
  | 10 => block346
  | 11 => block347
  | 12 => block348
  | 13 => block349
  | 14 => block350
  | 15 => block351
  | _ => #[]

def blockGroup22 : ℕ → Array IndexedEntry
  | 0 => block352
  | 1 => block353
  | 2 => block354
  | 3 => block355
  | 4 => block356
  | 5 => block357
  | 6 => block358
  | 7 => block359
  | 8 => block360
  | 9 => block361
  | 10 => block362
  | 11 => block363
  | 12 => block364
  | 13 => block365
  | 14 => block366
  | 15 => block367
  | _ => #[]

def blockGroup23 : ℕ → Array IndexedEntry
  | 0 => block368
  | 1 => block369
  | 2 => block370
  | 3 => block371
  | 4 => block372
  | 5 => block373
  | 6 => block374
  | 7 => block375
  | 8 => block376
  | 9 => block377
  | 10 => block378
  | 11 => block379
  | 12 => block380
  | 13 => block381
  | 14 => block382
  | 15 => block383
  | _ => #[]

def blockGroup24 : ℕ → Array IndexedEntry
  | 0 => block384
  | 1 => block385
  | 2 => block386
  | 3 => block387
  | 4 => block388
  | 5 => block389
  | 6 => block390
  | 7 => block391
  | 8 => block392
  | 9 => block393
  | 10 => block394
  | 11 => block395
  | 12 => block396
  | 13 => block397
  | 14 => block398
  | 15 => block399
  | _ => #[]

def blockGroup25 : ℕ → Array IndexedEntry
  | 0 => block400
  | 1 => block401
  | 2 => block402
  | 3 => block403
  | 4 => block404
  | 5 => block405
  | 6 => block406
  | 7 => block407
  | 8 => block408
  | 9 => block409
  | 10 => block410
  | 11 => block411
  | 12 => block412
  | 13 => block413
  | 14 => block414
  | 15 => block415
  | _ => #[]

def blockGroup26 : ℕ → Array IndexedEntry
  | 0 => block416
  | 1 => block417
  | 2 => block418
  | 3 => block419
  | 4 => block420
  | 5 => block421
  | 6 => block422
  | 7 => block423
  | 8 => block424
  | 9 => block425
  | 10 => block426
  | 11 => block427
  | 12 => block428
  | 13 => block429
  | 14 => block430
  | 15 => block431
  | _ => #[]

def blockGroup27 : ℕ → Array IndexedEntry
  | 0 => block432
  | 1 => block433
  | 2 => block434
  | 3 => block435
  | 4 => block436
  | 5 => block437
  | 6 => block438
  | 7 => block439
  | 8 => block440
  | 9 => block441
  | 10 => block442
  | 11 => block443
  | 12 => block444
  | 13 => block445
  | 14 => block446
  | 15 => block447
  | _ => #[]

def blockGroup28 : ℕ → Array IndexedEntry
  | 0 => block448
  | 1 => block449
  | 2 => block450
  | 3 => block451
  | 4 => block452
  | 5 => block453
  | 6 => block454
  | 7 => block455
  | 8 => block456
  | 9 => block457
  | 10 => block458
  | 11 => block459
  | 12 => block460
  | 13 => block461
  | 14 => block462
  | 15 => block463
  | _ => #[]

def blockGroup29 : ℕ → Array IndexedEntry
  | 0 => block464
  | 1 => block465
  | 2 => block466
  | 3 => block467
  | 4 => block468
  | 5 => block469
  | 6 => block470
  | 7 => block471
  | 8 => block472
  | 9 => block473
  | 10 => block474
  | 11 => block475
  | 12 => block476
  | 13 => block477
  | 14 => block478
  | 15 => block479
  | _ => #[]

def blockGroup30 : ℕ → Array IndexedEntry
  | 0 => block480
  | 1 => block481
  | 2 => block482
  | 3 => block483
  | 4 => block484
  | 5 => block485
  | 6 => block486
  | 7 => block487
  | 8 => block488
  | 9 => block489
  | 10 => block490
  | 11 => block491
  | 12 => block492
  | 13 => block493
  | 14 => block494
  | 15 => block495
  | _ => #[]

def blockGroup31 : ℕ → Array IndexedEntry
  | 0 => block496
  | 1 => block497
  | 2 => block498
  | 3 => block499
  | 4 => block500
  | 5 => block501
  | 6 => block502
  | 7 => block503
  | 8 => block504
  | 9 => block505
  | 10 => block506
  | 11 => block507
  | 12 => block508
  | 13 => block509
  | 14 => block510
  | 15 => block511
  | _ => #[]

def blockGroup32 : ℕ → Array IndexedEntry
  | 0 => block512
  | 1 => block513
  | 2 => block514
  | 3 => block515
  | 4 => block516
  | 5 => block517
  | 6 => block518
  | 7 => block519
  | 8 => block520
  | 9 => block521
  | 10 => block522
  | 11 => block523
  | 12 => block524
  | 13 => block525
  | 14 => block526
  | 15 => block527
  | _ => #[]

def blockGroup33 : ℕ → Array IndexedEntry
  | 0 => block528
  | 1 => block529
  | 2 => block530
  | 3 => block531
  | 4 => block532
  | 5 => block533
  | 6 => block534
  | 7 => block535
  | 8 => block536
  | 9 => block537
  | 10 => block538
  | 11 => block539
  | 12 => block540
  | 13 => block541
  | 14 => block542
  | 15 => block543
  | _ => #[]

def blockGroup34 : ℕ → Array IndexedEntry
  | 0 => block544
  | 1 => block545
  | 2 => block546
  | 3 => block547
  | 4 => block548
  | 5 => block549
  | 6 => block550
  | 7 => block551
  | 8 => block552
  | 9 => block553
  | 10 => block554
  | 11 => block555
  | 12 => block556
  | 13 => block557
  | 14 => block558
  | 15 => block559
  | _ => #[]

def blockGroup35 : ℕ → Array IndexedEntry
  | 0 => block560
  | 1 => block561
  | 2 => block562
  | 3 => block563
  | 4 => block564
  | 5 => block565
  | 6 => block566
  | 7 => block567
  | 8 => block568
  | 9 => block569
  | 10 => block570
  | 11 => block571
  | 12 => block572
  | 13 => block573
  | 14 => block574
  | 15 => block575
  | _ => #[]

def blockGroup36 : ℕ → Array IndexedEntry
  | 0 => block576
  | 1 => block577
  | 2 => block578
  | 3 => block579
  | 4 => block580
  | 5 => block581
  | 6 => block582
  | 7 => block583
  | 8 => block584
  | 9 => block585
  | 10 => block586
  | 11 => block587
  | 12 => block588
  | 13 => block589
  | 14 => block590
  | 15 => block591
  | _ => #[]

def blockGroup37 : ℕ → Array IndexedEntry
  | 0 => block592
  | 1 => block593
  | 2 => block594
  | 3 => block595
  | 4 => block596
  | 5 => block597
  | 6 => block598
  | 7 => block599
  | 8 => block600
  | 9 => block601
  | 10 => block602
  | 11 => block603
  | 12 => block604
  | 13 => block605
  | 14 => block606
  | 15 => block607
  | _ => #[]

def blockGroup38 : ℕ → Array IndexedEntry
  | 0 => block608
  | 1 => block609
  | 2 => block610
  | 3 => block611
  | 4 => block612
  | 5 => block613
  | 6 => block614
  | 7 => block615
  | 8 => block616
  | 9 => block617
  | 10 => block618
  | 11 => block619
  | 12 => block620
  | 13 => block621
  | 14 => block622
  | 15 => block623
  | _ => #[]

def blockGroup39 : ℕ → Array IndexedEntry
  | 0 => block624
  | 1 => block625
  | 2 => block626
  | 3 => block627
  | 4 => block628
  | 5 => block629
  | 6 => block630
  | 7 => block631
  | 8 => block632
  | 9 => block633
  | 10 => block634
  | 11 => block635
  | 12 => block636
  | 13 => block637
  | 14 => block638
  | 15 => block639
  | _ => #[]

def blockGroup40 : ℕ → Array IndexedEntry
  | 0 => block640
  | 1 => block641
  | 2 => block642
  | 3 => block643
  | 4 => block644
  | 5 => block645
  | 6 => block646
  | 7 => block647
  | 8 => block648
  | 9 => block649
  | 10 => block650
  | 11 => block651
  | 12 => block652
  | 13 => block653
  | 14 => block654
  | 15 => block655
  | _ => #[]

def blockGroup41 : ℕ → Array IndexedEntry
  | 0 => block656
  | 1 => block657
  | 2 => block658
  | 3 => block659
  | 4 => block660
  | 5 => block661
  | 6 => block662
  | 7 => block663
  | 8 => block664
  | 9 => block665
  | 10 => block666
  | 11 => block667
  | 12 => block668
  | 13 => block669
  | 14 => block670
  | 15 => block671
  | _ => #[]

def blockGroup42 : ℕ → Array IndexedEntry
  | 0 => block672
  | 1 => block673
  | 2 => block674
  | 3 => block675
  | 4 => block676
  | 5 => block677
  | 6 => block678
  | 7 => block679
  | 8 => block680
  | 9 => block681
  | 10 => block682
  | 11 => block683
  | 12 => block684
  | 13 => block685
  | 14 => block686
  | 15 => block687
  | _ => #[]

def blockGroup43 : ℕ → Array IndexedEntry
  | 0 => block688
  | 1 => block689
  | 2 => block690
  | 3 => block691
  | 4 => block692
  | 5 => block693
  | 6 => block694
  | 7 => block695
  | 8 => block696
  | 9 => block697
  | 10 => block698
  | 11 => block699
  | 12 => block700
  | 13 => block701
  | 14 => block702
  | 15 => block703
  | _ => #[]

def blockGroup44 : ℕ → Array IndexedEntry
  | 0 => block704
  | 1 => block705
  | 2 => block706
  | 3 => block707
  | 4 => block708
  | 5 => block709
  | 6 => block710
  | 7 => block711
  | 8 => block712
  | 9 => block713
  | 10 => block714
  | 11 => block715
  | 12 => block716
  | 13 => block717
  | 14 => block718
  | 15 => block719
  | _ => #[]

def blockGroup45 : ℕ → Array IndexedEntry
  | 0 => block720
  | 1 => block721
  | 2 => block722
  | 3 => block723
  | 4 => block724
  | 5 => block725
  | 6 => block726
  | 7 => block727
  | 8 => block728
  | 9 => block729
  | 10 => block730
  | 11 => block731
  | 12 => block732
  | 13 => block733
  | 14 => block734
  | 15 => block735
  | _ => #[]

def blockGroup46 : ℕ → Array IndexedEntry
  | 0 => block736
  | 1 => block737
  | 2 => block738
  | 3 => block739
  | 4 => block740
  | 5 => block741
  | 6 => block742
  | 7 => block743
  | 8 => block744
  | 9 => block745
  | 10 => block746
  | 11 => block747
  | 12 => block748
  | 13 => block749
  | 14 => block750
  | 15 => block751
  | _ => #[]

def blockGroup47 : ℕ → Array IndexedEntry
  | 0 => block752
  | 1 => block753
  | 2 => block754
  | 3 => block755
  | 4 => block756
  | 5 => block757
  | 6 => block758
  | 7 => block759
  | 8 => block760
  | 9 => block761
  | 10 => block762
  | 11 => block763
  | 12 => block764
  | 13 => block765
  | 14 => block766
  | 15 => block767
  | _ => #[]

def blockGroup48 : ℕ → Array IndexedEntry
  | 0 => block768
  | 1 => block769
  | 2 => block770
  | 3 => block771
  | 4 => block772
  | 5 => block773
  | 6 => block774
  | 7 => block775
  | 8 => block776
  | 9 => block777
  | 10 => block778
  | 11 => block779
  | 12 => block780
  | 13 => block781
  | 14 => block782
  | 15 => block783
  | _ => #[]

def blockGroup49 : ℕ → Array IndexedEntry
  | 0 => block784
  | 1 => block785
  | 2 => block786
  | 3 => block787
  | 4 => block788
  | 5 => block789
  | 6 => block790
  | 7 => block791
  | 8 => block792
  | 9 => block793
  | 10 => block794
  | 11 => block795
  | 12 => block796
  | 13 => block797
  | 14 => block798
  | 15 => block799
  | _ => #[]

def blockGroup50 : ℕ → Array IndexedEntry
  | 0 => block800
  | 1 => block801
  | 2 => block802
  | 3 => block803
  | 4 => block804
  | 5 => block805
  | 6 => block806
  | 7 => block807
  | 8 => block808
  | 9 => block809
  | 10 => block810
  | 11 => block811
  | 12 => block812
  | 13 => block813
  | 14 => block814
  | 15 => block815
  | _ => #[]

def blockGroup51 : ℕ → Array IndexedEntry
  | 0 => block816
  | 1 => block817
  | 2 => block818
  | 3 => block819
  | 4 => block820
  | 5 => block821
  | 6 => block822
  | 7 => block823
  | 8 => block824
  | 9 => block825
  | 10 => block826
  | 11 => block827
  | 12 => block828
  | 13 => block829
  | 14 => block830
  | 15 => block831
  | _ => #[]

def blockGroup52 : ℕ → Array IndexedEntry
  | 0 => block832
  | 1 => block833
  | 2 => block834
  | 3 => block835
  | 4 => block836
  | 5 => block837
  | 6 => block838
  | 7 => block839
  | 8 => block840
  | 9 => block841
  | 10 => block842
  | 11 => block843
  | 12 => block844
  | 13 => block845
  | 14 => block846
  | 15 => block847
  | _ => #[]

def blockGroup53 : ℕ → Array IndexedEntry
  | 0 => block848
  | 1 => block849
  | 2 => block850
  | 3 => block851
  | 4 => block852
  | 5 => block853
  | 6 => block854
  | 7 => block855
  | 8 => block856
  | 9 => block857
  | 10 => block858
  | 11 => block859
  | 12 => block860
  | 13 => block861
  | 14 => block862
  | 15 => block863
  | _ => #[]

def blockGroup54 : ℕ → Array IndexedEntry
  | 0 => block864
  | 1 => block865
  | 2 => block866
  | 3 => block867
  | 4 => block868
  | 5 => block869
  | 6 => block870
  | 7 => block871
  | 8 => block872
  | 9 => block873
  | 10 => block874
  | 11 => block875
  | 12 => block876
  | 13 => block877
  | 14 => block878
  | 15 => block879
  | _ => #[]

def blockGroup55 : ℕ → Array IndexedEntry
  | 0 => block880
  | 1 => block881
  | 2 => block882
  | 3 => block883
  | 4 => block884
  | 5 => block885
  | 6 => block886
  | 7 => block887
  | 8 => block888
  | 9 => block889
  | 10 => block890
  | 11 => block891
  | 12 => block892
  | 13 => block893
  | 14 => block894
  | 15 => block895
  | _ => #[]

def blockGroup56 : ℕ → Array IndexedEntry
  | 0 => block896
  | 1 => block897
  | 2 => block898
  | 3 => block899
  | 4 => block900
  | 5 => block901
  | 6 => block902
  | 7 => block903
  | 8 => block904
  | 9 => block905
  | 10 => block906
  | 11 => block907
  | 12 => block908
  | 13 => block909
  | 14 => block910
  | 15 => block911
  | _ => #[]

def blockGroup57 : ℕ → Array IndexedEntry
  | 0 => block912
  | 1 => block913
  | 2 => block914
  | 3 => block915
  | 4 => block916
  | 5 => block917
  | 6 => block918
  | 7 => block919
  | 8 => block920
  | 9 => block921
  | 10 => block922
  | 11 => block923
  | 12 => block924
  | 13 => block925
  | 14 => block926
  | 15 => block927
  | _ => #[]

def blockGroup58 : ℕ → Array IndexedEntry
  | 0 => block928
  | 1 => block929
  | 2 => block930
  | 3 => block931
  | 4 => block932
  | 5 => block933
  | 6 => block934
  | 7 => block935
  | 8 => block936
  | 9 => block937
  | 10 => block938
  | 11 => block939
  | 12 => block940
  | 13 => block941
  | 14 => block942
  | 15 => block943
  | _ => #[]

def blockGroup59 : ℕ → Array IndexedEntry
  | 0 => block944
  | 1 => block945
  | 2 => block946
  | 3 => block947
  | 4 => block948
  | 5 => block949
  | 6 => block950
  | 7 => block951
  | 8 => block952
  | 9 => block953
  | 10 => block954
  | 11 => block955
  | 12 => block956
  | 13 => block957
  | 14 => block958
  | 15 => block959
  | _ => #[]

def blockGroup60 : ℕ → Array IndexedEntry
  | 0 => block960
  | 1 => block961
  | 2 => block962
  | 3 => block963
  | 4 => block964
  | 5 => block965
  | 6 => block966
  | 7 => block967
  | 8 => block968
  | 9 => block969
  | 10 => block970
  | 11 => block971
  | 12 => block972
  | 13 => block973
  | 14 => block974
  | 15 => block975
  | _ => #[]

def blockGroup61 : ℕ → Array IndexedEntry
  | 0 => block976
  | 1 => block977
  | 2 => block978
  | 3 => block979
  | 4 => block980
  | 5 => block981
  | 6 => block982
  | 7 => block983
  | 8 => block984
  | 9 => block985
  | 10 => block986
  | 11 => block987
  | 12 => block988
  | 13 => block989
  | 14 => block990
  | 15 => block991
  | _ => #[]

def blockGroup62 : ℕ → Array IndexedEntry
  | 0 => block992
  | 1 => block993
  | 2 => block994
  | 3 => block995
  | 4 => block996
  | 5 => block997
  | 6 => block998
  | 7 => block999
  | 8 => block1000
  | 9 => block1001
  | 10 => block1002
  | 11 => block1003
  | 12 => block1004
  | 13 => block1005
  | 14 => block1006
  | 15 => block1007
  | _ => #[]

def blockGroup63 : ℕ → Array IndexedEntry
  | 0 => block1008
  | 1 => block1009
  | 2 => block1010
  | 3 => block1011
  | 4 => block1012
  | 5 => block1013
  | 6 => block1014
  | 7 => block1015
  | 8 => block1016
  | 9 => block1017
  | 10 => block1018
  | 11 => block1019
  | 12 => block1020
  | 13 => block1021
  | 14 => block1022
  | 15 => block1023
  | _ => #[]

def blockGroup64 : ℕ → Array IndexedEntry
  | 0 => block1024
  | 1 => block1025
  | 2 => block1026
  | 3 => block1027
  | 4 => block1028
  | 5 => block1029
  | 6 => block1030
  | 7 => block1031
  | 8 => block1032
  | 9 => block1033
  | 10 => block1034
  | 11 => block1035
  | 12 => block1036
  | 13 => block1037
  | 14 => block1038
  | 15 => block1039
  | _ => #[]

def blockGroup65 : ℕ → Array IndexedEntry
  | 0 => block1040
  | 1 => block1041
  | 2 => block1042
  | 3 => block1043
  | 4 => block1044
  | 5 => block1045
  | 6 => block1046
  | 7 => block1047
  | 8 => block1048
  | 9 => block1049
  | 10 => block1050
  | 11 => block1051
  | 12 => block1052
  | 13 => block1053
  | 14 => block1054
  | 15 => block1055
  | _ => #[]

def blockGroup66 : ℕ → Array IndexedEntry
  | 0 => block1056
  | 1 => block1057
  | 2 => block1058
  | 3 => block1059
  | 4 => block1060
  | 5 => block1061
  | 6 => block1062
  | 7 => block1063
  | 8 => block1064
  | 9 => block1065
  | 10 => block1066
  | 11 => block1067
  | 12 => block1068
  | 13 => block1069
  | 14 => block1070
  | 15 => block1071
  | _ => #[]

def blockGroup67 : ℕ → Array IndexedEntry
  | 0 => block1072
  | 1 => block1073
  | 2 => block1074
  | 3 => block1075
  | 4 => block1076
  | 5 => block1077
  | 6 => block1078
  | 7 => block1079
  | 8 => block1080
  | 9 => block1081
  | 10 => block1082
  | 11 => block1083
  | 12 => block1084
  | 13 => block1085
  | 14 => block1086
  | 15 => block1087
  | _ => #[]

def blockGroup68 : ℕ → Array IndexedEntry
  | 0 => block1088
  | 1 => block1089
  | 2 => block1090
  | 3 => block1091
  | 4 => block1092
  | 5 => block1093
  | 6 => block1094
  | 7 => block1095
  | 8 => block1096
  | 9 => block1097
  | 10 => block1098
  | 11 => block1099
  | 12 => block1100
  | 13 => block1101
  | 14 => block1102
  | 15 => block1103
  | _ => #[]

def blockGroup69 : ℕ → Array IndexedEntry
  | 0 => block1104
  | 1 => block1105
  | 2 => block1106
  | 3 => block1107
  | 4 => block1108
  | 5 => block1109
  | 6 => block1110
  | 7 => block1111
  | 8 => block1112
  | 9 => block1113
  | 10 => block1114
  | 11 => block1115
  | 12 => block1116
  | 13 => block1117
  | 14 => block1118
  | 15 => block1119
  | _ => #[]

def blockGroup70 : ℕ → Array IndexedEntry
  | 0 => block1120
  | 1 => block1121
  | 2 => block1122
  | 3 => block1123
  | 4 => block1124
  | 5 => block1125
  | 6 => block1126
  | 7 => block1127
  | 8 => block1128
  | 9 => block1129
  | 10 => block1130
  | 11 => block1131
  | 12 => block1132
  | 13 => block1133
  | 14 => block1134
  | 15 => block1135
  | _ => #[]

def blockGroup71 : ℕ → Array IndexedEntry
  | 0 => block1136
  | 1 => block1137
  | 2 => block1138
  | 3 => block1139
  | 4 => block1140
  | 5 => block1141
  | 6 => block1142
  | 7 => block1143
  | 8 => block1144
  | 9 => block1145
  | 10 => block1146
  | 11 => block1147
  | 12 => block1148
  | 13 => block1149
  | 14 => block1150
  | 15 => block1151
  | _ => #[]

def blockGroup72 : ℕ → Array IndexedEntry
  | 0 => block1152
  | 1 => block1153
  | 2 => block1154
  | 3 => block1155
  | 4 => block1156
  | 5 => block1157
  | 6 => block1158
  | 7 => block1159
  | 8 => block1160
  | 9 => block1161
  | 10 => block1162
  | 11 => block1163
  | 12 => block1164
  | 13 => block1165
  | 14 => block1166
  | 15 => block1167
  | _ => #[]

def blockGroup73 : ℕ → Array IndexedEntry
  | 0 => block1168
  | 1 => block1169
  | 2 => block1170
  | 3 => block1171
  | 4 => block1172
  | 5 => block1173
  | 6 => block1174
  | 7 => block1175
  | 8 => block1176
  | 9 => block1177
  | 10 => block1178
  | 11 => block1179
  | 12 => block1180
  | 13 => block1181
  | 14 => block1182
  | 15 => block1183
  | _ => #[]

def blockGroup74 : ℕ → Array IndexedEntry
  | 0 => block1184
  | 1 => block1185
  | 2 => block1186
  | 3 => block1187
  | 4 => block1188
  | 5 => block1189
  | 6 => block1190
  | 7 => block1191
  | 8 => block1192
  | 9 => block1193
  | 10 => block1194
  | 11 => block1195
  | 12 => block1196
  | 13 => block1197
  | 14 => block1198
  | 15 => block1199
  | _ => #[]

def blockGroup75 : ℕ → Array IndexedEntry
  | 0 => block1200
  | 1 => block1201
  | 2 => block1202
  | 3 => block1203
  | 4 => block1204
  | 5 => block1205
  | 6 => block1206
  | 7 => block1207
  | 8 => block1208
  | 9 => block1209
  | 10 => block1210
  | 11 => block1211
  | 12 => block1212
  | 13 => block1213
  | 14 => block1214
  | 15 => block1215
  | _ => #[]

def blockGroup76 : ℕ → Array IndexedEntry
  | 0 => block1216
  | 1 => block1217
  | 2 => block1218
  | 3 => block1219
  | 4 => block1220
  | 5 => block1221
  | 6 => block1222
  | 7 => block1223
  | 8 => block1224
  | 9 => block1225
  | 10 => block1226
  | 11 => block1227
  | 12 => block1228
  | 13 => block1229
  | 14 => block1230
  | 15 => block1231
  | _ => #[]

def blockGroup77 : ℕ → Array IndexedEntry
  | 0 => block1232
  | 1 => block1233
  | 2 => block1234
  | 3 => block1235
  | 4 => block1236
  | 5 => block1237
  | 6 => block1238
  | 7 => block1239
  | 8 => block1240
  | 9 => block1241
  | 10 => block1242
  | 11 => block1243
  | 12 => block1244
  | 13 => block1245
  | 14 => block1246
  | 15 => block1247
  | _ => #[]

def blockGroup78 : ℕ → Array IndexedEntry
  | 0 => block1248
  | 1 => block1249
  | 2 => block1250
  | 3 => block1251
  | 4 => block1252
  | 5 => block1253
  | 6 => block1254
  | 7 => block1255
  | 8 => block1256
  | 9 => block1257
  | 10 => block1258
  | 11 => block1259
  | 12 => block1260
  | 13 => block1261
  | 14 => block1262
  | 15 => block1263
  | _ => #[]

def blockGroup79 : ℕ → Array IndexedEntry
  | 0 => block1264
  | 1 => block1265
  | 2 => block1266
  | 3 => block1267
  | 4 => block1268
  | 5 => block1269
  | 6 => block1270
  | 7 => block1271
  | 8 => block1272
  | 9 => block1273
  | 10 => block1274
  | 11 => block1275
  | 12 => block1276
  | 13 => block1277
  | 14 => block1278
  | 15 => block1279
  | _ => #[]

def blockGroup80 : ℕ → Array IndexedEntry
  | 0 => block1280
  | 1 => block1281
  | 2 => block1282
  | 3 => block1283
  | 4 => block1284
  | 5 => block1285
  | 6 => block1286
  | 7 => block1287
  | 8 => block1288
  | 9 => block1289
  | 10 => block1290
  | 11 => block1291
  | 12 => block1292
  | 13 => block1293
  | 14 => block1294
  | 15 => block1295
  | _ => #[]

def blockGroup81 : ℕ → Array IndexedEntry
  | 0 => block1296
  | 1 => block1297
  | 2 => block1298
  | 3 => block1299
  | 4 => block1300
  | 5 => block1301
  | 6 => block1302
  | 7 => block1303
  | 8 => block1304
  | 9 => block1305
  | 10 => block1306
  | 11 => block1307
  | 12 => block1308
  | 13 => block1309
  | 14 => block1310
  | 15 => block1311
  | _ => #[]

def blockGroup82 : ℕ → Array IndexedEntry
  | 0 => block1312
  | 1 => block1313
  | 2 => block1314
  | 3 => block1315
  | 4 => block1316
  | 5 => block1317
  | 6 => block1318
  | 7 => block1319
  | 8 => block1320
  | 9 => block1321
  | 10 => block1322
  | 11 => block1323
  | 12 => block1324
  | 13 => block1325
  | 14 => block1326
  | 15 => block1327
  | _ => #[]

def blockGroup83 : ℕ → Array IndexedEntry
  | 0 => block1328
  | 1 => block1329
  | 2 => block1330
  | 3 => block1331
  | 4 => block1332
  | 5 => block1333
  | 6 => block1334
  | 7 => block1335
  | 8 => block1336
  | 9 => block1337
  | 10 => block1338
  | 11 => block1339
  | 12 => block1340
  | 13 => block1341
  | 14 => block1342
  | 15 => block1343
  | _ => #[]

def blockGroup84 : ℕ → Array IndexedEntry
  | 0 => block1344
  | 1 => block1345
  | 2 => block1346
  | 3 => block1347
  | 4 => block1348
  | 5 => block1349
  | 6 => block1350
  | 7 => block1351
  | 8 => block1352
  | 9 => block1353
  | 10 => block1354
  | 11 => block1355
  | 12 => block1356
  | 13 => block1357
  | 14 => block1358
  | 15 => block1359
  | _ => #[]

def blockGroup85 : ℕ → Array IndexedEntry
  | 0 => block1360
  | 1 => block1361
  | 2 => block1362
  | 3 => block1363
  | 4 => block1364
  | 5 => block1365
  | 6 => block1366
  | 7 => block1367
  | 8 => block1368
  | 9 => block1369
  | 10 => block1370
  | 11 => block1371
  | 12 => block1372
  | 13 => block1373
  | 14 => block1374
  | 15 => block1375
  | _ => #[]

def blockGroup86 : ℕ → Array IndexedEntry
  | 0 => block1376
  | 1 => block1377
  | 2 => block1378
  | 3 => block1379
  | 4 => block1380
  | 5 => block1381
  | 6 => block1382
  | 7 => block1383
  | 8 => block1384
  | 9 => block1385
  | 10 => block1386
  | 11 => block1387
  | 12 => block1388
  | 13 => block1389
  | 14 => block1390
  | 15 => block1391
  | _ => #[]

def blockGroup87 : ℕ → Array IndexedEntry
  | 0 => block1392
  | 1 => block1393
  | _ => #[]

def superGroup0 (k : ℕ) : Array IndexedEntry :=
  match (k/16)%16 with
  | 0 => blockGroup0 (k%16)
  | 1 => blockGroup1 (k%16)
  | 2 => blockGroup2 (k%16)
  | 3 => blockGroup3 (k%16)
  | 4 => blockGroup4 (k%16)
  | 5 => blockGroup5 (k%16)
  | 6 => blockGroup6 (k%16)
  | 7 => blockGroup7 (k%16)
  | 8 => blockGroup8 (k%16)
  | 9 => blockGroup9 (k%16)
  | 10 => blockGroup10 (k%16)
  | 11 => blockGroup11 (k%16)
  | 12 => blockGroup12 (k%16)
  | 13 => blockGroup13 (k%16)
  | 14 => blockGroup14 (k%16)
  | 15 => blockGroup15 (k%16)
  | _ => #[]

def superGroup1 (k : ℕ) : Array IndexedEntry :=
  match (k/16)%16 with
  | 0 => blockGroup16 (k%16)
  | 1 => blockGroup17 (k%16)
  | 2 => blockGroup18 (k%16)
  | 3 => blockGroup19 (k%16)
  | 4 => blockGroup20 (k%16)
  | 5 => blockGroup21 (k%16)
  | 6 => blockGroup22 (k%16)
  | 7 => blockGroup23 (k%16)
  | 8 => blockGroup24 (k%16)
  | 9 => blockGroup25 (k%16)
  | 10 => blockGroup26 (k%16)
  | 11 => blockGroup27 (k%16)
  | 12 => blockGroup28 (k%16)
  | 13 => blockGroup29 (k%16)
  | 14 => blockGroup30 (k%16)
  | 15 => blockGroup31 (k%16)
  | _ => #[]

def superGroup2 (k : ℕ) : Array IndexedEntry :=
  match (k/16)%16 with
  | 0 => blockGroup32 (k%16)
  | 1 => blockGroup33 (k%16)
  | 2 => blockGroup34 (k%16)
  | 3 => blockGroup35 (k%16)
  | 4 => blockGroup36 (k%16)
  | 5 => blockGroup37 (k%16)
  | 6 => blockGroup38 (k%16)
  | 7 => blockGroup39 (k%16)
  | 8 => blockGroup40 (k%16)
  | 9 => blockGroup41 (k%16)
  | 10 => blockGroup42 (k%16)
  | 11 => blockGroup43 (k%16)
  | 12 => blockGroup44 (k%16)
  | 13 => blockGroup45 (k%16)
  | 14 => blockGroup46 (k%16)
  | 15 => blockGroup47 (k%16)
  | _ => #[]

def superGroup3 (k : ℕ) : Array IndexedEntry :=
  match (k/16)%16 with
  | 0 => blockGroup48 (k%16)
  | 1 => blockGroup49 (k%16)
  | 2 => blockGroup50 (k%16)
  | 3 => blockGroup51 (k%16)
  | 4 => blockGroup52 (k%16)
  | 5 => blockGroup53 (k%16)
  | 6 => blockGroup54 (k%16)
  | 7 => blockGroup55 (k%16)
  | 8 => blockGroup56 (k%16)
  | 9 => blockGroup57 (k%16)
  | 10 => blockGroup58 (k%16)
  | 11 => blockGroup59 (k%16)
  | 12 => blockGroup60 (k%16)
  | 13 => blockGroup61 (k%16)
  | 14 => blockGroup62 (k%16)
  | 15 => blockGroup63 (k%16)
  | _ => #[]

def superGroup4 (k : ℕ) : Array IndexedEntry :=
  match (k/16)%16 with
  | 0 => blockGroup64 (k%16)
  | 1 => blockGroup65 (k%16)
  | 2 => blockGroup66 (k%16)
  | 3 => blockGroup67 (k%16)
  | 4 => blockGroup68 (k%16)
  | 5 => blockGroup69 (k%16)
  | 6 => blockGroup70 (k%16)
  | 7 => blockGroup71 (k%16)
  | 8 => blockGroup72 (k%16)
  | 9 => blockGroup73 (k%16)
  | 10 => blockGroup74 (k%16)
  | 11 => blockGroup75 (k%16)
  | 12 => blockGroup76 (k%16)
  | 13 => blockGroup77 (k%16)
  | 14 => blockGroup78 (k%16)
  | 15 => blockGroup79 (k%16)
  | _ => #[]

def superGroup5 (k : ℕ) : Array IndexedEntry :=
  match (k/16)%16 with
  | 0 => blockGroup80 (k%16)
  | 1 => blockGroup81 (k%16)
  | 2 => blockGroup82 (k%16)
  | 3 => blockGroup83 (k%16)
  | 4 => blockGroup84 (k%16)
  | 5 => blockGroup85 (k%16)
  | 6 => blockGroup86 (k%16)
  | 7 => blockGroup87 (k%16)
  | _ => #[]

def table : IndexedTable := ⟨22292, fun k =>
  match k/256 with
  | 0 => superGroup0 k
  | 1 => superGroup1 k
  | 2 => superGroup2 k
  | 3 => superGroup3 k
  | 4 => superGroup4 k
  | 5 => superGroup5 k
  | _ => #[]⟩

def classes : List Shape := [[14],[13,1],[12,2],[12,1,1],[11,3],[11,2,1],[11,1,1,1],[10,4],[10,3,1],[10,2,2],[10,2,1,1],[10,1,1,1,1],[9,5],[9,4,1],[9,3,2],[9,3,1,1],[9,2,2,1],[9,2,1,1,1],[9,1,1,1,1,1],[8,6],[8,5,1],[8,4,2],[8,4,1,1],[8,3,3],[8,3,2,1],[8,3,1,1,1],[8,2,2,2],[8,2,2,1,1],[8,2,1,1,1,1],[8,1,1,1,1,1,1],[7,7],[7,6,1],[7,5,2],[7,5,1,1],[7,4,3],[7,4,2,1],[7,4,1,1,1],[7,3,3,1],[7,3,2,2],[7,3,2,1,1],[7,3,1,1,1,1],[7,2,2,2,1],[7,2,2,1,1,1],[7,2,1,1,1,1,1],[7,1,1,1,1,1,1,1],[6,6,2],[6,6,1,1],[6,5,3],[6,5,2,1],[6,5,1,1,1],[6,4,4],[6,4,3,1],[6,4,2,2],[6,4,2,1,1],[6,4,1,1,1,1],[6,3,3,2],[6,3,3,1,1],[6,3,2,2,1],[6,3,2,1,1,1],[6,3,1,1,1,1,1],[6,2,2,2,2],[6,2,2,2,1,1],[6,2,2,1,1,1,1],[6,2,1,1,1,1,1,1],[6,1,1,1,1,1,1,1,1],[5,5,4],[5,5,3,1],[5,5,2,2],[5,5,2,1,1],[5,5,1,1,1,1],[5,4,4,1],[5,4,3,2],[5,4,3,1,1],[5,4,2,2,1],[5,4,2,1,1,1],[5,4,1,1,1,1,1],[5,3,3,3],[5,3,3,2,1],[5,3,3,1,1,1],[5,3,2,2,2],[5,3,2,2,1,1],[5,3,2,1,1,1,1],[5,3,1,1,1,1,1,1],[5,2,2,2,2,1],[5,2,2,2,1,1,1],[5,2,2,1,1,1,1,1],[5,2,1,1,1,1,1,1,1],[5,1,1,1,1,1,1,1,1,1],[4,4,4,2],[4,4,4,1,1],[4,4,3,3],[4,4,3,2,1],[4,4,3,1,1,1],[4,4,2,2,2],[4,4,2,2,1,1],[4,4,2,1,1,1,1],[4,4,1,1,1,1,1,1],[4,3,3,3,1],[4,3,3,2,2],[4,3,3,2,1,1],[4,3,3,1,1,1,1],[4,3,2,2,2,1],[4,3,2,2,1,1,1],[4,3,2,1,1,1,1,1],[4,3,1,1,1,1,1,1,1],[4,2,2,2,2,2],[4,2,2,2,2,1,1],[4,2,2,2,1,1,1,1],[4,2,2,1,1,1,1,1,1],[4,2,1,1,1,1,1,1,1,1],[4,1,1,1,1,1,1,1,1,1,1],[3,3,3,3,2],[3,3,3,3,1,1],[3,3,3,2,2,1],[3,3,3,2,1,1,1],[3,3,3,1,1,1,1,1],[3,3,2,2,2,2],[3,3,2,2,2,1,1],[3,3,2,2,1,1,1,1],[3,3,2,1,1,1,1,1,1],[3,3,1,1,1,1,1,1,1,1],[3,2,2,2,2,2,1],[3,2,2,2,2,1,1,1],[3,2,2,2,1,1,1,1,1],[3,2,2,1,1,1,1,1,1,1],[3,2,1,1,1,1,1,1,1,1,1],[3,1,1,1,1,1,1,1,1,1,1,1],[2,2,2,2,2,2,2],[2,2,2,2,2,2,1,1],[2,2,2,2,2,1,1,1,1],[2,2,2,2,1,1,1,1,1,1],[2,2,2,1,1,1,1,1,1,1,1],[2,2,1,1,1,1,1,1,1,1,1,1],[2,1,1,1,1,1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1,1,1,1,1,1,1]]

def refs0 : List ℕ := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99,101,103,105,107,109,111,113,115,117,119,121,123,125,127,129,131,133,135,137,139,141,143,145,147,149,151,153,155,157,159,161,163,165,167,169,171,173,175,177,179,181,183,185,187,189,191,193,195,197,199,201,203,205,207,209,211,213,215,217,219,221,223,225,227,229,231,233,235,237,239,241,243,245,247,249,251,253,255,257,259,261,263,265,267,269]

def refs1 : List ℕ := [270,271,273,275,277,279,281,283,285,287,289,291,293,295,297,299,301,303,305,307,309,311,313,315,317,319,321,323,325,327,329,331,333,335,337,339,341,343,345,347,349,351,353,355,357,359,361,363,365,367,369,371,373,375,377,379,381,383,385,387,389,391,393,395,397,399,401,403,405,407,409,411,413,415,417,419,421,423,425,427,429,431,433,435,437,439,441,443,445,447,449,451,453,455,457,459,461,463,465,467,469,471,473,475,477,479,481,483,485,487,489,491,493,495,497,499,501,503,505,507,509,511,513,515,517,519,521,523,525,527,529,531,533,535,537]

def refs2 : List ℕ := [538,539,540,541,542,543,544,546,548,550,552,554,556,558,560,562,564,566,568,570,572,574,576,578,580,582,584,586,588,590,592,594,596,598,600,602,604,606,608,610,612,614,616,618,620,622,624,626,628,630,632,634,636,638,640,642,644,646,648,650,652,654,656,658,660,662,664,666,668,670,672,674,676,678,680,682,684,686,688,690,692,694,696,698,700,702,704,706,708,710,712,714,716,718,720,722,724,726,728,730,732,734,736,738,740,742,744,746,748,750,752,754,756,758,760,762,764,766,768,770,772,774,776,778,780,782,784,786,788,790,792,794,796,798,800]

def refs3 : List ℕ := [801,802,803,804,806,808,810,812,814,816,818,820,822,824,826,828,830,832,834,836,838,840,842,844,846,848,850,852,854,856,858,860,862,864,866,868,870,872,874,876,878,880,882,884,886,888,890,892,894,896,898,900,902,904,906,908,910,912,914,916,918,920,922,924,926,928,930,932,934,936,938,940,942,944,946,948,950,952,954,956,958,960,962,964,966,968,970,972,974,976,978,980,982,984,986,988,990,992,994,996,998,1000,1002,1004,1006,1008,1010,1012,1014,1016,1018,1020,1022,1024,1026,1028,1030,1032,1034,1036,1038,1040,1042,1044,1046,1048,1050,1052,1054,1056,1058,1060,1062,1064,1066]

def refs4 : List ℕ := [1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1087,1089,1091,1093,1095,1097,1099,1101,1103,1105,1107,1109,1111,1113,1115,1117,1119,1121,1123,1125,1127,1129,1131,1133,1135,1137,1139,1141,1143,1145,1147,1149,1151,1153,1155,1157,1159,1161,1163,1165,1167,1169,1171,1173,1175,1177,1179,1181,1183,1185,1187,1189,1191,1193,1195,1197,1199,1201,1203,1205,1207,1209,1211,1213,1215,1217,1219,1221,1223,1225,1227,1229,1231,1233,1235,1237,1239,1241,1243,1245,1247,1249,1251,1253,1255,1257,1259,1261,1263,1265,1267,1269,1271,1273,1275,1277,1279,1281,1283,1285,1287,1289,1291,1293,1295,1297,1299,1301,1303,1305,1307,1309,1311,1313,1315,1317]

def refs5 : List ℕ := [1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1331,1333,1335,1337,1339,1341,1343,1345,1347,1349,1351,1353,1355,1357,1359,1361,1363,1365,1367,1369,1371,1373,1375,1377,1379,1381,1383,1385,1387,1389,1391,1393,1395,1397,1399,1401,1403,1405,1407,1409,1411,1413,1415,1417,1419,1421,1423,1425,1427,1429,1431,1433,1435,1437,1439,1441,1443,1445,1447,1449,1451,1453,1455,1457,1459,1461,1463,1465,1467,1469,1471,1473,1475,1477,1479,1481,1483,1485,1487,1489,1491,1493,1495,1497,1499,1501,1503,1505,1507,1509,1511,1513,1515,1517,1519,1521,1523,1525,1527,1529,1531,1533,1535,1537,1539,1541,1543,1545,1547,1549,1551,1553,1555,1557,1559,1561,1563,1565,1567,1569,1571,1573,1575]

def refs6 : List ℕ := [1576,1577,1578,1579,1580,1581,1582,1584,1586,1588,1590,1592,1594,1596,1598,1600,1602,1604,1606,1608,1610,1612,1614,1616,1618,1620,1622,1624,1626,1628,1630,1632,1634,1636,1638,1640,1642,1644,1646,1648,1650,1652,1654,1656,1658,1660,1662,1664,1666,1668,1670,1672,1674,1676,1678,1680,1682,1684,1686,1688,1690,1692,1694,1696,1698,1700,1702,1704,1706,1708,1710,1712,1714,1716,1718,1720,1722,1724,1726,1728,1730,1732,1734,1736,1738,1740,1742,1744,1746,1748,1750,1752,1754,1756,1758,1760,1762,1764,1766,1768,1770,1772,1774,1776,1778,1780,1782,1784,1786,1788,1790,1792,1794,1796,1798,1800,1802,1804,1806,1808,1810,1812,1814,1816,1818,1820,1822,1824,1826,1828,1830,1832,1834,1836,1838]

def refs7 : List ℕ := [1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1885,1887,1889,1891,1893,1895,1897,1899,1901,1903,1905,1907,1909,1911,1913,1915,1917,1919,1921,1923,1925,1927,1929,1931,1933,1935,1937,1939,1941,1943,1945,1947,1949,1951,1953,1955,1957,1959,1961,1963,1965,1967,1969,1971,1973,1975,1977,1979,1981,1983,1985,1987,1989,1991,1993,1995,1997,1999,2001,2003,2005,2007,2009,2011,2013,2015,2017,2019,2021,2023,2025,2027,2029,2031,2033,2035,2037,2039,2041,2043,2045,2047,2049,2051,2053,2055,2057,2059,2061,2063]

def refs8 : List ℕ := [2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087,2088,2089,2090,2091,2092,2093,2095,2097,2099,2101,2103,2105,2107,2109,2111,2113,2115,2117,2119,2121,2123,2125,2127,2129,2131,2133,2135,2137,2139,2141,2143,2145,2147,2149,2151,2153,2155,2157,2159,2161,2163,2165,2167,2169,2171,2173,2175,2177,2179,2181,2183,2185,2187,2189,2191,2193,2195,2197,2199,2201,2203,2205,2207,2209,2211,2213,2215,2217,2219,2221,2223,2225,2227,2229,2231,2233,2235,2237,2239,2241,2243,2245,2247,2249,2251,2253,2255,2257,2259,2261,2263,2265,2267,2269,2271,2273,2275,2277,2279,2281,2283,2285,2287,2289,2291,2293,2295,2297,2299,2301,2303]

def refs9 : List ℕ := [2304,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2324,2326,2328,2330,2332,2334,2336,2338,2340,2342,2344,2346,2348,2350,2352,2354,2356,2358,2360,2362,2364,2366,2368,2370,2372,2374,2376,2378,2380,2382,2384,2386,2388,2390,2392,2394,2396,2398,2400,2402,2404,2406,2408,2410,2412,2414,2416,2418,2420,2422,2424,2426,2428,2430,2432,2434,2436,2438,2440,2442,2444,2446,2448,2450,2452,2454,2456,2458,2460,2462,2464,2466,2468,2470,2472,2474,2476,2478,2480,2482,2484,2486,2488,2490,2492,2494,2496,2498,2500,2502,2504,2506,2508,2510,2512,2514,2516,2518,2520,2522,2524,2526,2528,2530,2532,2534,2536,2538,2540,2542,2544,2546,2548,2550,2552,2554]

def refs10 : List ℕ := [2555,2556,2557,2558,2559,2560,2561,2562,2563,2564,2565,2566,2567,2568,2569,2570,2571,2572,2573,2575,2577,2579,2581,2583,2585,2587,2589,2591,2593,2595,2597,2599,2601,2603,2605,2607,2609,2611,2613,2615,2617,2619,2621,2623,2625,2627,2629,2631,2633,2635,2637,2639,2641,2643,2645,2647,2649,2651,2653,2655,2657,2659,2661,2663,2665,2667,2669,2671,2673,2675,2677,2679,2681,2683,2685,2687,2689,2691,2693,2695,2697,2699,2701,2703,2705,2707,2709,2711,2713,2715,2717,2719,2721,2723,2725,2727,2729,2731,2733,2735,2737,2739,2741,2743,2745,2747,2749,2751,2753,2755,2757,2759,2761,2763,2765,2767,2769,2771,2773,2775,2777,2779,2781,2783,2785,2787,2789,2791,2793,2795,2797,2799,2801,2803,2805]

def refs11 : List ℕ := [2806,2807,2808,2809,2810,2811,2812,2813,2814,2815,2816,2817,2819,2821,2823,2825,2827,2829,2831,2833,2835,2837,2839,2841,2843,2845,2847,2849,2851,2853,2855,2857,2859,2861,2863,2865,2867,2869,2871,2873,2875,2877,2879,2881,2883,2885,2887,2889,2891,2893,2895,2897,2899,2901,2903,2905,2907,2909,2911,2913,2915,2917,2919,2921,2923,2925,2927,2929,2931,2933,2935,2937,2939,2941,2943,2945,2947,2949,2951,2953,2955,2957,2959,2961,2963,2965,2967,2969,2971,2973,2975,2977,2979,2981,2983,2985,2987,2989,2991,2993,2995,2997,2999,3001,3003,3005,3007,3009,3011,3013,3015,3017,3019,3021,3023,3025,3027,3029,3031,3033,3035,3037,3039,3041,3043,3045,3047,3049,3051,3053,3055,3057,3059,3061,3063]

def refs12 : List ℕ := [3064,3065,3066,3067,3068,3069,3070,3071,3072,3073,3074,3075,3076,3077,3078,3079,3080,3081,3082,3083,3084,3085,3086,3087,3088,3089,3090,3091,3092,3093,3094,3095,3096,3097,3098,3099,3100,3101,3102,3103,3104,3105,3106,3107,3108,3109,3110,3111,3112,3113,3114,3115,3116,3117,3118,3119,3120,3121,3122,3123,3124,3125,3126,3127,3128,3129,3130,3131,3132,3133,3134,3135,3136,3137,3138,3139,3140,3141,3142,3143,3144,3145,3146,3147,3148,3149,3150,3151,3153,3155,3157,3159,3161,3163,3165,3167,3169,3171,3173,3175,3177,3179,3181,3183,3185,3187,3189,3191,3193,3195,3197,3199,3201,3203,3205,3207,3209,3211,3213,3215,3217,3219,3221,3223,3225,3227,3229,3231,3233,3235,3237,3239,3241,3243,3245]

def refs13 : List ℕ := [3246,3247,3248,3249,3250,3251,3252,3253,3254,3255,3256,3257,3258,3259,3260,3261,3262,3263,3264,3265,3266,3267,3268,3269,3270,3271,3272,3273,3274,3275,3276,3277,3278,3279,3280,3281,3282,3283,3284,3285,3286,3287,3288,3289,3290,3291,3292,3293,3294,3295,3296,3297,3298,3299,3300,3301,3302,3303,3304,3305,3306,3307,3308,3309,3310,3312,3314,3316,3318,3320,3322,3324,3326,3328,3330,3332,3334,3336,3338,3340,3342,3344,3346,3348,3350,3352,3354,3356,3358,3360,3362,3364,3366,3368,3370,3372,3374,3376,3378,3380,3382,3384,3386,3388,3390,3392,3394,3396,3398,3400,3402,3404,3406,3408,3410,3412,3414,3416,3418,3420,3422,3424,3426,3428,3430,3432,3434,3436,3438,3440,3442,3444,3446,3448,3450]

def refs14 : List ℕ := [3451,3452,3453,3454,3455,3456,3457,3458,3459,3460,3461,3462,3463,3464,3465,3466,3467,3468,3469,3470,3471,3472,3473,3474,3475,3476,3477,3478,3479,3480,3481,3482,3483,3484,3485,3486,3487,3488,3489,3490,3491,3492,3493,3494,3495,3497,3499,3501,3503,3505,3507,3509,3511,3513,3515,3517,3519,3521,3523,3525,3527,3529,3531,3533,3535,3537,3539,3541,3543,3545,3547,3549,3551,3553,3555,3557,3559,3561,3563,3565,3567,3569,3571,3573,3575,3577,3579,3581,3583,3585,3587,3589,3591,3593,3595,3597,3599,3601,3603,3605,3607,3609,3611,3613,3615,3617,3619,3621,3623,3625,3627,3629,3631,3633,3635,3637,3639,3641,3643,3645,3647,3649,3651,3653,3655,3657,3659,3661,3663,3665,3667,3669,3671,3673,3675]

def refs15 : List ℕ := [3676,3677,3678,3679,3680,3681,3682,3683,3684,3685,3686,3687,3688,3689,3690,3691,3692,3693,3694,3695,3696,3697,3698,3699,3700,3701,3702,3703,3704,3705,3706,3707,3708,3709,3710,3711,3712,3713,3714,3715,3716,3717,3718,3719,3720,3722,3724,3726,3728,3730,3732,3734,3736,3738,3740,3742,3744,3746,3748,3750,3752,3754,3756,3758,3760,3762,3764,3766,3768,3770,3772,3774,3776,3778,3780,3782,3784,3786,3788,3790,3792,3794,3796,3798,3800,3802,3804,3806,3808,3810,3812,3814,3816,3818,3820,3822,3824,3826,3828,3830,3832,3834,3836,3838,3840,3842,3844,3846,3848,3850,3852,3854,3856,3858,3860,3862,3864,3866,3868,3870,3872,3874,3876,3878,3880,3882,3884,3886,3888,3890,3892,3894,3896,3898,3900]

def refs16 : List ℕ := [3901,3902,3903,3904,3905,3906,3907,3908,3909,3910,3911,3912,3913,3914,3915,3916,3917,3918,3919,3920,3921,3922,3923,3924,3925,3926,3927,3928,3929,3930,3932,3934,3936,3938,3940,3942,3944,3946,3948,3950,3952,3954,3956,3958,3960,3962,3964,3966,3968,3970,3972,3974,3976,3978,3980,3982,3984,3986,3988,3990,3992,3994,3996,3998,4000,4002,4004,4006,4008,4010,4012,4014,4016,4018,4020,4022,4024,4026,4028,4030,4032,4034,4036,4038,4040,4042,4044,4046,4048,4050,4052,4054,4056,4058,4060,4062,4064,4066,4068,4070,4072,4074,4076,4078,4080,4082,4084,4086,4088,4090,4092,4094,4096,4098,4100,4102,4104,4106,4108,4110,4112,4114,4116,4118,4120,4122,4124,4126,4128,4130,4132,4134,4136,4138,4140]

def refs17 : List ℕ := [4141,4142,4143,4144,4145,4146,4147,4148,4149,4150,4151,4152,4153,4154,4155,4156,4157,4158,4159,4160,4161,4162,4163,4164,4165,4166,4167,4168,4169,4170,4172,4174,4176,4178,4180,4182,4184,4186,4188,4190,4192,4194,4196,4198,4200,4202,4204,4206,4208,4210,4212,4214,4216,4218,4220,4222,4224,4226,4228,4230,4232,4234,4236,4238,4240,4242,4244,4246,4248,4250,4252,4254,4256,4258,4260,4262,4264,4266,4268,4270,4272,4274,4276,4278,4280,4282,4284,4286,4288,4290,4292,4294,4296,4298,4300,4302,4304,4306,4308,4310,4312,4314,4316,4318,4320,4322,4324,4326,4328,4330,4332,4334,4336,4338,4340,4342,4344,4346,4348,4350,4352,4354,4356,4358,4360,4362,4364,4366,4368,4370,4372,4374,4376,4378,4380]

def refs18 : List ℕ := [4381,4382,4383,4384,4385,4386,4387,4388,4389,4390,4391,4392,4393,4394,4395,4396,4397,4398,4399,4401,4403,4405,4407,4409,4411,4413,4415,4417,4419,4421,4423,4425,4427,4429,4431,4433,4435,4437,4439,4441,4443,4445,4447,4449,4451,4453,4455,4457,4459,4461,4463,4465,4467,4469,4471,4473,4475,4477,4479,4481,4483,4485,4487,4489,4491,4493,4495,4497,4499,4501,4503,4505,4507,4509,4511,4513,4515,4517,4519,4521,4523,4525,4527,4529,4531,4533,4535,4537,4539,4541,4543,4545,4547,4549,4551,4553,4555,4557,4559,4561,4563,4565,4567,4569,4571,4573,4575,4577,4579,4581,4583,4585,4587,4589,4591,4593,4595,4597,4599,4601,4603,4605,4607,4609,4611,4613,4615,4617,4619,4621,4623,4625,4627,4629,4631]

def refs19 : List ℕ := [4632,4633,4634,4635,4636,4637,4638,4639,4640,4641,4642,4643,4644,4645,4646,4647,4648,4649,4650,4651,4652,4653,4654,4655,4656,4657,4658,4659,4660,4661,4662,4663,4664,4665,4666,4667,4668,4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696,4697,4698,4699,4700,4701,4702,4703,4704,4705,4706,4707,4708,4709,4710,4711,4712,4713,4714,4715,4716,4717,4718,4719,4720,4721,4722,4723,4724,4725,4726,4727,4728,4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756,4757,4758,4760,4762,4764,4766,4768,4770,4772,4774]

def refs20 : List ℕ := [4775,4776,4777,4778,4779,4780,4781,4782,4783,4784,4785,4786,4787,4788,4789,4790,4791,4792,4793,4794,4795,4796,4797,4798,4799,4800,4801,4802,4803,4804,4805,4806,4807,4808,4809,4810,4811,4812,4813,4814,4815,4816,4817,4818,4819,4820,4821,4822,4823,4824,4825,4826,4827,4828,4829,4830,4831,4832,4833,4834,4835,4836,4837,4838,4839,4840,4841,4842,4843,4844,4845,4846,4847,4848,4849,4850,4851,4852,4853,4854,4855,4856,4857,4858,4859,4860,4861,4862,4863,4864,4865,4866,4867,4868,4869,4870,4871,4872,4873,4874,4875,4876,4877,4878,4879,4880,4881,4882,4883,4884,4885,4887,4889,4891,4893,4895,4897,4899,4901,4903,4905,4907,4909,4911,4913,4915,4917,4919,4921,4923,4925,4927,4929,4931,4933]

def refs21 : List ℕ := [4934,4935,4936,4937,4938,4939,4940,4941,4942,4943,4944,4945,4946,4947,4948,4949,4950,4951,4952,4953,4954,4955,4956,4957,4958,4959,4960,4961,4962,4963,4964,4965,4966,4967,4968,4969,4970,4971,4972,4973,4974,4975,4976,4977,4978,4979,4980,4981,4982,4983,4984,4985,4986,4987,4988,4989,4990,4991,4992,4993,4994,4995,4996,4997,4998,4999,5000,5001,5002,5003,5004,5005,5006,5007,5008,5009,5010,5011,5012,5013,5014,5015,5016,5017,5018,5019,5020,5021,5023,5025,5027,5029,5031,5033,5035,5037,5039,5041,5043,5045,5047,5049,5051,5053,5055,5057,5059,5061,5063,5065,5067,5069,5071,5073,5075,5077,5079,5081,5083,5085,5087,5089,5091,5093,5095,5097,5099,5101,5103,5105,5107,5109,5111,5113,5115]

def refs22 : List ℕ := [5116,5117,5118,5119,5120,5121,5122,5123,5124,5125,5126,5127,5128,5129,5130,5131,5132,5133,5134,5135,5136,5137,5138,5139,5140,5141,5142,5143,5144,5145,5146,5147,5148,5149,5150,5151,5152,5153,5154,5155,5156,5157,5158,5159,5160,5161,5162,5163,5164,5165,5166,5167,5168,5169,5170,5171,5172,5173,5174,5175,5176,5177,5178,5179,5180,5181,5182,5183,5184,5185,5186,5187,5188,5189,5190,5191,5192,5193,5194,5195,5196,5197,5198,5199,5200,5201,5202,5203,5205,5207,5209,5211,5213,5215,5217,5219,5221,5223,5225,5227,5229,5231,5233,5235,5237,5239,5241,5243,5245,5247,5249,5251,5253,5255,5257,5259,5261,5263,5265,5267,5269,5271,5273,5275,5277,5279,5281,5283,5285,5287,5289,5291,5293,5295,5297]

def refs23 : List ℕ := [5298,5299,5300,5301,5302,5303,5304,5305,5306,5307,5308,5309,5310,5311,5312,5313,5314,5315,5316,5317,5318,5319,5320,5321,5322,5323,5324,5325,5326,5327,5328,5329,5330,5331,5332,5333,5334,5335,5336,5337,5338,5339,5340,5341,5342,5343,5344,5345,5346,5347,5348,5349,5350,5351,5352,5353,5354,5355,5356,5357,5358,5359,5360,5361,5362,5364,5366,5368,5370,5372,5374,5376,5378,5380,5382,5384,5386,5388,5390,5392,5394,5396,5398,5400,5402,5404,5406,5408,5410,5412,5414,5416,5418,5420,5422,5424,5426,5428,5430,5432,5434,5436,5438,5440,5442,5444,5446,5448,5450,5452,5454,5456,5458,5460,5462,5464,5466,5468,5470,5472,5474,5476,5478,5480,5482,5484,5486,5488,5490,5492,5494,5496,5498,5500,5502]

def refs24 : List ℕ := [5503,5504,5505,5506,5507,5508,5509,5510,5511,5512,5513,5514,5515,5516,5517,5518,5519,5520,5521,5522,5523,5524,5525,5526,5527,5528,5529,5530,5531,5532,5533,5534,5535,5536,5537,5538,5539,5540,5541,5542,5543,5544,5545,5546,5547,5548,5549,5550,5551,5552,5553,5554,5555,5556,5557,5558,5559,5560,5561,5562,5563,5564,5565,5566,5567,5569,5571,5573,5575,5577,5579,5581,5583,5585,5587,5589,5591,5593,5595,5597,5599,5601,5603,5605,5607,5609,5611,5613,5615,5617,5619,5621,5623,5625,5627,5629,5631,5633,5635,5637,5639,5641,5643,5645,5647,5649,5651,5653,5655,5657,5659,5661,5663,5665,5667,5669,5671,5673,5675,5677,5679,5681,5683,5685,5687,5689,5691,5693,5695,5697,5699,5701,5703,5705,5707]

def refs25 : List ℕ := [5708,5709,5710,5711,5712,5713,5714,5715,5716,5717,5718,5719,5720,5721,5722,5723,5724,5725,5726,5727,5728,5729,5730,5731,5732,5733,5734,5735,5736,5737,5738,5739,5740,5741,5742,5743,5744,5745,5746,5747,5748,5749,5750,5751,5752,5753,5754,5755,5756,5757,5758,5759,5760,5761,5762,5763,5764,5765,5766,5767,5768,5769,5770,5771,5772,5774,5776,5778,5780,5782,5784,5786,5788,5790,5792,5794,5796,5798,5800,5802,5804,5806,5808,5810,5812,5814,5816,5818,5820,5822,5824,5826,5828,5830,5832,5834,5836,5838,5840,5842,5844,5846,5848,5850,5852,5854,5856,5858,5860,5862,5864,5866,5868,5870,5872,5874,5876,5878,5880,5882,5884,5886,5888,5890,5892,5894,5896,5898,5900,5902,5904,5906,5908,5910,5912]

def refs26 : List ℕ := [5913,5914,5915,5916,5917,5918,5919,5920,5921,5922,5923,5924,5925,5926,5927,5928,5929,5930,5931,5932,5933,5934,5935,5936,5937,5938,5939,5940,5941,5942,5943,5944,5945,5946,5947,5948,5949,5950,5951,5952,5953,5954,5955,5956,5957,5959,5961,5963,5965,5967,5969,5971,5973,5975,5977,5979,5981,5983,5985,5987,5989,5991,5993,5995,5997,5999,6001,6003,6005,6007,6009,6011,6013,6015,6017,6019,6021,6023,6025,6027,6029,6031,6033,6035,6037,6039,6041,6043,6045,6047,6049,6051,6053,6055,6057,6059,6061,6063,6065,6067,6069,6071,6073,6075,6077,6079,6081,6083,6085,6087,6089,6091,6093,6095,6097,6099,6101,6103,6105,6107,6109,6111,6113,6115,6117,6119,6121,6123,6125,6127,6129,6131,6133,6135,6137]

def refs27 : List ℕ := [6138,6139,6140,6141,6142,6143,6144,6145,6146,6147,6148,6149,6150,6151,6152,6153,6154,6155,6156,6157,6158,6159,6160,6161,6162,6163,6164,6165,6166,6167,6168,6169,6170,6171,6172,6173,6174,6175,6176,6177,6178,6179,6180,6181,6182,6184,6186,6188,6190,6192,6194,6196,6198,6200,6202,6204,6206,6208,6210,6212,6214,6216,6218,6220,6222,6224,6226,6228,6230,6232,6234,6236,6238,6240,6242,6244,6246,6248,6250,6252,6254,6256,6258,6260,6262,6264,6266,6268,6270,6272,6274,6276,6278,6280,6282,6284,6286,6288,6290,6292,6294,6296,6298,6300,6302,6304,6306,6308,6310,6312,6314,6316,6318,6320,6322,6324,6326,6328,6330,6332,6334,6336,6338,6340,6342,6344,6346,6348,6350,6352,6354,6356,6358,6360,6362]

def refs28 : List ℕ := [6363,6364,6365,6366,6367,6368,6369,6370,6371,6372,6373,6374,6375,6376,6377,6378,6379,6380,6381,6382,6383,6384,6385,6386,6387,6388,6389,6390,6391,6392,6393,6394,6395,6396,6397,6398,6399,6400,6401,6402,6403,6404,6405,6406,6407,6409,6411,6413,6415,6417,6419,6421,6423,6425,6427,6429,6431,6433,6435,6437,6439,6441,6443,6445,6447,6449,6451,6453,6455,6457,6459,6461,6463,6465,6467,6469,6471,6473,6475,6477,6479,6481,6483,6485,6487,6489,6491,6493,6495,6497,6499,6501,6503,6505,6507,6509,6511,6513,6515,6517,6519,6521,6523,6525,6527,6529,6531,6533,6535,6537,6539,6541,6543,6545,6547,6549,6551,6553,6555,6557,6559,6561,6563,6565,6567,6569,6571,6573,6575,6577,6579,6581,6583,6585,6587]

def refs29 : List ℕ := [6588,6589,6590,6591,6592,6593,6594,6595,6596,6597,6598,6599,6600,6601,6602,6603,6604,6605,6606,6607,6608,6609,6610,6611,6612,6613,6614,6615,6616,6617,6619,6621,6623,6625,6627,6629,6631,6633,6635,6637,6639,6641,6643,6645,6647,6649,6651,6653,6655,6657,6659,6661,6663,6665,6667,6669,6671,6673,6675,6677,6679,6681,6683,6685,6687,6689,6691,6693,6695,6697,6699,6701,6703,6705,6707,6709,6711,6713,6715,6717,6719,6721,6723,6725,6727,6729,6731,6733,6735,6737,6739,6741,6743,6745,6747,6749,6751,6753,6755,6757,6759,6761,6763,6765,6767,6769,6771,6773,6775,6777,6779,6781,6783,6785,6787,6789,6791,6793,6795,6797,6799,6801,6803,6805,6807,6809,6811,6813,6815,6817,6819,6821,6823,6825,6827]

def refs30 : List ℕ := [6828,6829,6830,6831,6832,6833,6834,6835,6836,6837,6838,6839,6840,6841,6842,6843,6844,6845,6846,6847,6848,6849,6850,6851,6852,6853,6854,6855,6856,6857,6858,6859,6860,6861,6862,6863,6864,6865,6866,6867,6868,6869,6870,6871,6872,6873,6874,6875,6876,6877,6878,6879,6880,6881,6882,6883,6884,6885,6886,6887,6888,6889,6890,6891,6892,6893,6894,6895,6896,6897,6898,6899,6900,6901,6902,6903,6904,6905,6906,6907,6908,6909,6910,6911,6912,6913,6914,6915,6916,6917,6918,6919,6920,6921,6922,6923,6924,6925,6926,6927,6928,6929,6930,6931,6932,6933,6934,6935,6936,6937,6938,6939,6940,6941,6942,6943,6944,6945,6946,6947,6948,6949,6950,6951,6952,6953,6954,6955,6956,6957,6958,6959,6960,6961,6962]

def refs31 : List ℕ := [6963,6964,6965,6966,6967,6968,6969,6970,6971,6972,6973,6974,6975,6976,6977,6978,6979,6980,6981,6982,6983,6984,6985,6986,6987,6988,6989,6990,6991,6992,6993,6994,6995,6996,6997,6998,6999,7000,7001,7002,7003,7004,7005,7006,7007,7008,7009,7010,7011,7012,7013,7014,7015,7016,7017,7018,7019,7020,7021,7022,7023,7024,7025,7026,7027,7028,7029,7030,7031,7032,7033,7034,7035,7036,7037,7038,7039,7040,7041,7042,7043,7044,7045,7046,7047,7048,7049,7050,7051,7052,7053,7054,7055,7056,7057,7058,7059,7060,7061,7062,7063,7064,7065,7066,7067,7068,7069,7070,7071,7072,7073,7074,7075,7076,7077,7078,7079,7080,7081,7082,7083,7084,7085,7086,7087,7088,7089,7090,7091,7092,7093,7094,7095,7096,7098]

def refs32 : List ℕ := [7099,7100,7101,7102,7103,7104,7105,7106,7107,7108,7109,7110,7111,7112,7113,7114,7115,7116,7117,7118,7119,7120,7121,7122,7123,7124,7125,7126,7127,7128,7129,7130,7131,7132,7133,7134,7135,7136,7137,7138,7139,7140,7141,7142,7143,7144,7145,7146,7147,7148,7149,7150,7151,7152,7153,7154,7155,7156,7157,7158,7159,7160,7161,7162,7163,7164,7165,7166,7167,7168,7169,7170,7171,7172,7173,7174,7175,7176,7177,7178,7179,7180,7181,7182,7183,7184,7185,7186,7187,7188,7189,7190,7191,7192,7193,7194,7195,7196,7197,7198,7199,7200,7201,7202,7203,7204,7205,7206,7207,7208,7209,7210,7211,7212,7213,7214,7215,7216,7217,7218,7219,7220,7221,7222,7223,7224,7225,7227,7229,7231,7233,7235,7237,7239,7241]

def refs33 : List ℕ := [7242,7243,7244,7245,7246,7247,7248,7249,7250,7251,7252,7253,7254,7255,7256,7257,7258,7259,7260,7261,7262,7263,7264,7265,7266,7267,7268,7269,7270,7271,7272,7273,7274,7275,7276,7277,7278,7279,7280,7281,7282,7283,7284,7285,7286,7287,7288,7289,7290,7291,7292,7293,7294,7295,7296,7297,7298,7299,7300,7301,7302,7303,7304,7305,7306,7307,7308,7309,7310,7311,7312,7313,7314,7315,7316,7317,7318,7319,7320,7321,7322,7323,7324,7325,7326,7327,7328,7329,7330,7331,7332,7333,7334,7335,7336,7337,7338,7339,7340,7341,7342,7343,7344,7345,7346,7347,7348,7349,7350,7351,7352,7353,7354,7355,7356,7357,7358,7359,7360,7361,7362,7363,7364,7365,7366,7367,7368,7370,7372,7374,7376,7378,7380,7382,7384]

def refs34 : List ℕ := [7385,7386,7387,7388,7389,7390,7391,7392,7393,7394,7395,7396,7397,7398,7399,7400,7401,7402,7403,7404,7405,7406,7407,7408,7409,7410,7411,7412,7413,7414,7415,7416,7417,7418,7419,7420,7421,7422,7423,7424,7425,7426,7427,7428,7429,7430,7431,7432,7433,7434,7435,7436,7437,7438,7439,7440,7441,7442,7443,7444,7445,7446,7447,7448,7449,7450,7451,7452,7453,7454,7455,7456,7457,7458,7459,7460,7461,7462,7463,7464,7465,7466,7467,7468,7469,7470,7471,7472,7473,7474,7475,7476,7477,7478,7479,7480,7481,7482,7483,7484,7485,7486,7487,7488,7489,7490,7491,7492,7493,7494,7495,7497,7499,7501,7503,7505,7507,7509,7511,7513,7515,7517,7519,7521,7523,7525,7527,7529,7531,7533,7535,7537,7539,7541,7543]

def refs35 : List ℕ := [7544,7545,7546,7547,7548,7549,7550,7551,7552,7553,7554,7555,7556,7557,7558,7559,7560,7561,7562,7563,7564,7565,7566,7567,7568,7569,7570,7571,7572,7573,7574,7575,7576,7577,7578,7579,7580,7581,7582,7583,7584,7585,7586,7587,7588,7589,7590,7591,7592,7593,7594,7595,7596,7597,7598,7599,7600,7601,7602,7603,7604,7605,7606,7607,7608,7609,7610,7611,7612,7613,7614,7615,7616,7617,7618,7619,7620,7621,7622,7623,7624,7625,7626,7627,7628,7629,7630,7631,7632,7633,7634,7635,7636,7637,7638,7639,7640,7641,7642,7643,7644,7645,7646,7647,7648,7649,7650,7651,7652,7653,7654,7656,7658,7660,7662,7664,7666,7668,7670,7672,7674,7676,7678,7680,7682,7684,7686,7688,7690,7692,7694,7696,7698,7700,7702]

def refs36 : List ℕ := [7703,7704,7705,7706,7707,7708,7709,7710,7711,7712,7713,7714,7715,7716,7717,7718,7719,7720,7721,7722,7723,7724,7725,7726,7727,7728,7729,7730,7731,7732,7733,7734,7735,7736,7737,7738,7739,7740,7741,7742,7743,7744,7745,7746,7747,7748,7749,7750,7751,7752,7753,7754,7755,7756,7757,7758,7759,7760,7761,7762,7763,7764,7765,7766,7767,7768,7769,7770,7771,7772,7773,7774,7775,7776,7777,7778,7779,7780,7781,7782,7783,7784,7785,7786,7787,7788,7789,7790,7791,7792,7793,7794,7795,7796,7797,7798,7799,7800,7801,7802,7803,7804,7805,7806,7807,7808,7809,7810,7811,7812,7813,7815,7817,7819,7821,7823,7825,7827,7829,7831,7833,7835,7837,7839,7841,7843,7845,7847,7849,7851,7853,7855,7857,7859,7861]

def refs37 : List ℕ := [7862,7863,7864,7865,7866,7867,7868,7869,7870,7871,7872,7873,7874,7875,7876,7877,7878,7879,7880,7881,7882,7883,7884,7885,7886,7887,7888,7889,7890,7891,7892,7893,7894,7895,7896,7897,7898,7899,7900,7901,7902,7903,7904,7905,7906,7907,7908,7909,7910,7911,7912,7913,7914,7915,7916,7917,7918,7919,7920,7921,7922,7923,7924,7925,7926,7927,7928,7929,7930,7931,7932,7933,7934,7935,7936,7937,7938,7939,7940,7941,7942,7943,7944,7945,7946,7947,7948,7949,7951,7953,7955,7957,7959,7961,7963,7965,7967,7969,7971,7973,7975,7977,7979,7981,7983,7985,7987,7989,7991,7993,7995,7997,7999,8001,8003,8005,8007,8009,8011,8013,8015,8017,8019,8021,8023,8025,8027,8029,8031,8033,8035,8037,8039,8041,8043]

def refs38 : List ℕ := [8044,8045,8046,8047,8048,8049,8050,8051,8052,8053,8054,8055,8056,8057,8058,8059,8060,8061,8062,8063,8064,8065,8066,8067,8068,8069,8070,8071,8072,8073,8074,8075,8076,8077,8078,8079,8080,8081,8082,8083,8084,8085,8086,8087,8088,8089,8090,8091,8092,8093,8094,8095,8096,8097,8098,8099,8100,8101,8102,8103,8104,8105,8106,8107,8108,8109,8110,8111,8112,8113,8114,8115,8116,8117,8118,8119,8120,8121,8122,8123,8124,8125,8126,8127,8128,8129,8130,8131,8133,8135,8137,8139,8141,8143,8145,8147,8149,8151,8153,8155,8157,8159,8161,8163,8165,8167,8169,8171,8173,8175,8177,8179,8181,8183,8185,8187,8189,8191,8193,8195,8197,8199,8201,8203,8205,8207,8209,8211,8213,8215,8217,8219,8221,8223,8225]

def refs39 : List ℕ := [8226,8227,8228,8229,8230,8231,8232,8233,8234,8235,8236,8237,8238,8239,8240,8241,8242,8243,8244,8245,8246,8247,8248,8249,8250,8251,8252,8253,8254,8255,8256,8257,8258,8259,8260,8261,8262,8263,8264,8265,8266,8267,8268,8269,8270,8271,8272,8273,8274,8275,8276,8277,8278,8279,8280,8281,8282,8283,8284,8285,8286,8287,8288,8289,8290,8291,8292,8293,8294,8295,8296,8297,8298,8299,8300,8301,8302,8303,8304,8305,8306,8307,8308,8309,8310,8311,8312,8313,8315,8317,8319,8321,8323,8325,8327,8329,8331,8333,8335,8337,8339,8341,8343,8345,8347,8349,8351,8353,8355,8357,8359,8361,8363,8365,8367,8369,8371,8373,8375,8377,8379,8381,8383,8385,8387,8389,8391,8393,8395,8397,8399,8401,8403,8405,8407]

def refs40 : List ℕ := [8408,8409,8410,8411,8412,8413,8414,8415,8416,8417,8418,8419,8420,8421,8422,8423,8424,8425,8426,8427,8428,8429,8430,8431,8432,8433,8434,8435,8436,8437,8438,8439,8440,8441,8442,8443,8444,8445,8446,8447,8448,8449,8450,8451,8452,8453,8454,8455,8456,8457,8458,8459,8460,8461,8462,8463,8464,8465,8466,8467,8468,8469,8470,8471,8472,8473,8474,8475,8476,8477,8478,8479,8480,8481,8482,8483,8484,8485,8486,8487,8488,8489,8490,8491,8492,8493,8494,8495,8497,8499,8501,8503,8505,8507,8509,8511,8513,8515,8517,8519,8521,8523,8525,8527,8529,8531,8533,8535,8537,8539,8541,8543,8545,8547,8549,8551,8553,8555,8557,8559,8561,8563,8565,8567,8569,8571,8573,8575,8577,8579,8581,8583,8585,8587,8589]

def refs41 : List ℕ := [8590,8591,8592,8593,8594,8595,8596,8597,8598,8599,8600,8601,8602,8603,8604,8605,8606,8607,8608,8609,8610,8611,8612,8613,8614,8615,8616,8617,8618,8619,8620,8621,8622,8623,8624,8625,8626,8627,8628,8629,8630,8631,8632,8633,8634,8635,8636,8637,8638,8639,8640,8641,8642,8643,8644,8645,8646,8647,8648,8649,8650,8651,8652,8653,8654,8656,8658,8660,8662,8664,8666,8668,8670,8672,8674,8676,8678,8680,8682,8684,8686,8688,8690,8692,8694,8696,8698,8700,8702,8704,8706,8708,8710,8712,8714,8716,8718,8720,8722,8724,8726,8728,8730,8732,8734,8736,8738,8740,8742,8744,8746,8748,8750,8752,8754,8756,8758,8760,8762,8764,8766,8768,8770,8772,8774,8776,8778,8780,8782,8784,8786,8788,8790,8792,8794]

def refs42 : List ℕ := [8795,8796,8797,8798,8799,8800,8801,8802,8803,8804,8805,8806,8807,8808,8809,8810,8811,8812,8813,8814,8815,8816,8817,8818,8819,8820,8821,8822,8823,8824,8825,8826,8827,8828,8829,8830,8831,8832,8833,8834,8835,8836,8837,8838,8839,8840,8841,8842,8843,8844,8845,8846,8847,8848,8849,8850,8851,8852,8853,8854,8855,8856,8857,8858,8859,8861,8863,8865,8867,8869,8871,8873,8875,8877,8879,8881,8883,8885,8887,8889,8891,8893,8895,8897,8899,8901,8903,8905,8907,8909,8911,8913,8915,8917,8919,8921,8923,8925,8927,8929,8931,8933,8935,8937,8939,8941,8943,8945,8947,8949,8951,8953,8955,8957,8959,8961,8963,8965,8967,8969,8971,8973,8975,8977,8979,8981,8983,8985,8987,8989,8991,8993,8995,8997,8999]

def refs43 : List ℕ := [9000,9001,9002,9003,9004,9005,9006,9007,9008,9009,9010,9011,9012,9013,9014,9015,9016,9017,9018,9019,9020,9021,9022,9023,9024,9025,9026,9027,9028,9029,9030,9031,9032,9033,9034,9035,9036,9037,9038,9039,9040,9041,9042,9043,9044,9045,9046,9047,9048,9049,9050,9051,9052,9053,9054,9055,9056,9057,9058,9059,9060,9061,9062,9063,9064,9066,9068,9070,9072,9074,9076,9078,9080,9082,9084,9086,9088,9090,9092,9094,9096,9098,9100,9102,9104,9106,9108,9110,9112,9114,9116,9118,9120,9122,9124,9126,9128,9130,9132,9134,9136,9138,9140,9142,9144,9146,9148,9150,9152,9154,9156,9158,9160,9162,9164,9166,9168,9170,9172,9174,9176,9178,9180,9182,9184,9186,9188,9190,9192,9194,9196,9198,9200,9202,9204]

def refs44 : List ℕ := [9205,9206,9207,9208,9209,9210,9211,9212,9213,9214,9215,9216,9217,9218,9219,9220,9221,9222,9223,9224,9225,9226,9227,9228,9229,9230,9231,9232,9233,9234,9235,9236,9237,9238,9239,9240,9241,9242,9243,9244,9245,9246,9247,9248,9249,9251,9253,9255,9257,9259,9261,9263,9265,9267,9269,9271,9273,9275,9277,9279,9281,9283,9285,9287,9289,9291,9293,9295,9297,9299,9301,9303,9305,9307,9309,9311,9313,9315,9317,9319,9321,9323,9325,9327,9329,9331,9333,9335,9337,9339,9341,9343,9345,9347,9349,9351,9353,9355,9357,9359,9361,9363,9365,9367,9369,9371,9373,9375,9377,9379,9381,9383,9385,9387,9389,9391,9393,9395,9397,9399,9401,9403,9405,9407,9409,9411,9413,9415,9417,9419,9421,9423,9425,9427,9429]

def refs45 : List ℕ := [9430,9431,9432,9433,9434,9435,9436,9437,9438,9439,9440,9441,9442,9443,9444,9445,9446,9447,9448,9449,9450,9451,9452,9453,9454,9455,9456,9457,9458,9459,9460,9461,9462,9463,9464,9465,9466,9467,9468,9469,9470,9471,9472,9473,9474,9475,9476,9477,9478,9479,9480,9481,9482,9483,9484,9485,9486,9487,9488,9489,9490,9491,9492,9493,9494,9495,9496,9497,9498,9499,9500,9501,9502,9503,9504,9505,9506,9507,9508,9509,9510,9511,9512,9513,9514,9515,9516,9517,9518,9519,9520,9521,9522,9523,9524,9525,9526,9527,9528,9529,9530,9531,9532,9533,9534,9535,9536,9537,9538,9539,9540,9541,9542,9543,9544,9545,9546,9547,9548,9549,9550,9551,9552,9553,9554,9555,9556,9557,9558,9559,9560,9561,9562,9563,9564]

def refs46 : List ℕ := [9565,9566,9567,9568,9569,9570,9571,9572,9573,9574,9575,9576,9577,9578,9579,9580,9581,9582,9583,9584,9585,9586,9587,9588,9589,9590,9591,9592,9593,9594,9595,9596,9597,9598,9599,9600,9601,9602,9603,9604,9605,9606,9607,9608,9609,9610,9611,9612,9613,9614,9615,9616,9617,9618,9619,9620,9621,9622,9623,9624,9625,9626,9627,9628,9629,9630,9631,9632,9633,9634,9635,9636,9637,9638,9639,9640,9641,9642,9643,9644,9645,9646,9647,9648,9649,9650,9651,9652,9653,9654,9655,9656,9657,9658,9659,9660,9661,9662,9663,9664,9665,9666,9667,9668,9669,9670,9671,9672,9673,9674,9675,9676,9677,9678,9679,9680,9681,9682,9683,9684,9685,9686,9687,9688,9689,9690,9691,9692,9693,9694,9695,9696,9697,9698,9699]

def refs47 : List ℕ := [9700,9701,9702,9703,9704,9705,9706,9707,9708,9709,9710,9711,9712,9713,9714,9715,9716,9717,9718,9719,9720,9721,9722,9723,9724,9725,9726,9727,9728,9729,9730,9731,9732,9733,9734,9735,9736,9737,9738,9739,9740,9741,9742,9743,9744,9745,9746,9747,9748,9749,9750,9751,9752,9753,9754,9755,9756,9757,9758,9759,9760,9761,9762,9763,9764,9765,9766,9767,9768,9769,9770,9771,9772,9773,9774,9775,9776,9777,9778,9779,9780,9781,9782,9783,9784,9785,9786,9787,9788,9789,9790,9791,9792,9793,9794,9795,9796,9797,9798,9799,9800,9801,9802,9803,9804,9805,9806,9807,9808,9809,9810,9811,9812,9813,9814,9815,9816,9817,9818,9819,9820,9821,9822,9823,9824,9825,9826,9827,9828,9829,9830,9831,9832,9833,9835]

def refs48 : List ℕ := [9836,9837,9838,9839,9840,9841,9842,9843,9844,9845,9846,9847,9848,9849,9850,9851,9852,9853,9854,9855,9856,9857,9858,9859,9860,9861,9862,9863,9864,9865,9866,9867,9868,9869,9870,9871,9872,9873,9874,9875,9876,9877,9878,9879,9880,9881,9882,9883,9884,9885,9886,9887,9888,9889,9890,9891,9892,9893,9894,9895,9896,9897,9898,9899,9900,9901,9902,9903,9904,9905,9906,9907,9908,9909,9910,9911,9912,9913,9914,9915,9916,9917,9918,9919,9920,9921,9922,9923,9924,9925,9926,9927,9928,9929,9930,9931,9932,9933,9934,9935,9936,9937,9938,9939,9940,9941,9942,9943,9944,9945,9946,9947,9948,9949,9950,9951,9952,9953,9954,9955,9956,9957,9958,9959,9960,9961,9962,9963,9964,9965,9966,9967,9968,9969,9971]

def refs49 : List ℕ := [9972,9973,9974,9975,9976,9977,9978,9979,9980,9981,9982,9983,9984,9985,9986,9987,9988,9989,9990,9991,9992,9993,9994,9995,9996,9997,9998,9999,10000,10001,10002,10003,10004,10005,10006,10007,10008,10009,10010,10011,10012,10013,10014,10015,10016,10017,10018,10019,10020,10021,10022,10023,10024,10025,10026,10027,10028,10029,10030,10031,10032,10033,10034,10035,10036,10037,10038,10039,10040,10041,10042,10043,10044,10045,10046,10047,10048,10049,10050,10051,10052,10053,10054,10055,10056,10057,10058,10059,10060,10061,10062,10063,10064,10065,10066,10067,10068,10069,10070,10071,10072,10073,10074,10075,10076,10077,10078,10079,10080,10081,10082,10083,10084,10085,10086,10087,10088,10089,10090,10091,10092,10093,10094,10095,10096,10097,10098,10099,10100,10101,10102,10103,10104,10105,10107]

def refs50 : List ℕ := [10108,10109,10110,10111,10112,10113,10114,10115,10116,10117,10118,10119,10120,10121,10122,10123,10124,10125,10126,10127,10128,10129,10130,10131,10132,10133,10134,10135,10136,10137,10138,10139,10140,10141,10142,10143,10144,10145,10146,10147,10148,10149,10150,10151,10152,10153,10154,10155,10156,10157,10158,10159,10160,10161,10162,10163,10164,10165,10166,10167,10168,10169,10170,10171,10172,10173,10174,10175,10176,10177,10178,10179,10180,10181,10182,10183,10184,10185,10186,10187,10188,10189,10190,10191,10192,10193,10194,10195,10196,10197,10198,10199,10200,10201,10202,10203,10204,10205,10206,10207,10208,10209,10210,10211,10212,10213,10214,10215,10216,10217,10218,10219,10220,10221,10222,10223,10224,10225,10226,10227,10228,10229,10230,10231,10232,10233,10234,10236,10238,10240,10242,10244,10246,10248,10250]

def refs51 : List ℕ := [10251,10252,10253,10254,10255,10256,10257,10258,10259,10260,10261,10262,10263,10264,10265,10266,10267,10268,10269,10270,10271,10272,10273,10274,10275,10276,10277,10278,10279,10280,10281,10282,10283,10284,10285,10286,10287,10288,10289,10290,10291,10292,10293,10294,10295,10296,10297,10298,10299,10300,10301,10302,10303,10304,10305,10306,10307,10308,10309,10310,10311,10312,10313,10314,10315,10316,10317,10318,10319,10320,10321,10322,10323,10324,10325,10326,10327,10328,10329,10330,10331,10332,10333,10334,10335,10336,10337,10338,10339,10340,10341,10342,10343,10344,10345,10346,10347,10348,10349,10350,10351,10352,10353,10354,10355,10356,10357,10358,10359,10360,10361,10362,10363,10364,10365,10366,10367,10368,10369,10370,10371,10372,10373,10374,10375,10376,10377,10379,10381,10383,10385,10387,10389,10391,10393]

def refs52 : List ℕ := [10394,10395,10396,10397,10398,10399,10400,10401,10402,10403,10404,10405,10406,10407,10408,10409,10410,10411,10412,10413,10414,10415,10416,10417,10418,10419,10420,10421,10422,10423,10424,10425,10426,10427,10428,10429,10430,10431,10432,10433,10434,10435,10436,10437,10438,10439,10440,10441,10442,10443,10444,10445,10446,10447,10448,10449,10450,10451,10452,10453,10454,10455,10456,10457,10458,10459,10460,10461,10462,10463,10464,10465,10466,10467,10468,10469,10470,10471,10472,10473,10474,10475,10476,10477,10478,10479,10480,10481,10482,10483,10484,10485,10486,10487,10488,10489,10490,10491,10492,10493,10494,10495,10496,10497,10498,10499,10500,10501,10502,10503,10504,10505,10506,10507,10508,10509,10510,10511,10512,10513,10514,10515,10516,10517,10518,10519,10520,10522,10524,10526,10528,10530,10532,10534,10536]

def refs53 : List ℕ := [10537,10538,10539,10540,10541,10542,10543,10544,10545,10546,10547,10548,10549,10550,10551,10552,10553,10554,10555,10556,10557,10558,10559,10560,10561,10562,10563,10564,10565,10566,10567,10568,10569,10570,10571,10572,10573,10574,10575,10576,10577,10578,10579,10580,10581,10582,10583,10584,10585,10586,10587,10588,10589,10590,10591,10592,10593,10594,10595,10596,10597,10598,10599,10600,10601,10602,10603,10604,10605,10606,10607,10608,10609,10610,10611,10612,10613,10614,10615,10616,10617,10618,10619,10620,10621,10622,10623,10624,10625,10626,10627,10628,10629,10630,10631,10632,10633,10634,10635,10636,10637,10638,10639,10640,10641,10642,10643,10644,10645,10646,10647,10648,10649,10650,10651,10652,10653,10654,10655,10656,10657,10658,10659,10660,10661,10662,10663,10665,10667,10669,10671,10673,10675,10677,10679]

def refs54 : List ℕ := [10680,10681,10682,10683,10684,10685,10686,10687,10688,10689,10690,10691,10692,10693,10694,10695,10696,10697,10698,10699,10700,10701,10702,10703,10704,10705,10706,10707,10708,10709,10710,10711,10712,10713,10714,10715,10716,10717,10718,10719,10720,10721,10722,10723,10724,10725,10726,10727,10728,10729,10730,10731,10732,10733,10734,10735,10736,10737,10738,10739,10740,10741,10742,10743,10744,10745,10746,10747,10748,10749,10750,10751,10752,10753,10754,10755,10756,10757,10758,10759,10760,10761,10762,10763,10764,10765,10766,10767,10768,10769,10770,10771,10772,10773,10774,10775,10776,10777,10778,10779,10780,10781,10782,10783,10784,10785,10786,10787,10788,10789,10790,10791,10792,10793,10794,10795,10796,10797,10798,10799,10800,10801,10802,10803,10804,10805,10806,10808,10810,10812,10814,10816,10818,10820,10822]

def refs55 : List ℕ := [10823,10824,10825,10826,10827,10828,10829,10830,10831,10832,10833,10834,10835,10836,10837,10838,10839,10840,10841,10842,10843,10844,10845,10846,10847,10848,10849,10850,10851,10852,10853,10854,10855,10856,10857,10858,10859,10860,10861,10862,10863,10864,10865,10866,10867,10868,10869,10870,10871,10872,10873,10874,10875,10876,10877,10878,10879,10880,10881,10882,10883,10884,10885,10886,10887,10888,10889,10890,10891,10892,10893,10894,10895,10896,10897,10898,10899,10900,10901,10902,10903,10904,10905,10906,10907,10908,10909,10910,10911,10912,10913,10914,10915,10916,10917,10918,10919,10920,10921,10922,10923,10924,10925,10926,10927,10928,10929,10930,10931,10932,10933,10935,10937,10939,10941,10943,10945,10947,10949,10951,10953,10955,10957,10959,10961,10963,10965,10967,10969,10971,10973,10975,10977,10979,10981]

def refs56 : List ℕ := [10982,10983,10984,10985,10986,10987,10988,10989,10990,10991,10992,10993,10994,10995,10996,10997,10998,10999,11000,11001,11002,11003,11004,11005,11006,11007,11008,11009,11010,11011,11012,11013,11014,11015,11016,11017,11018,11019,11020,11021,11022,11023,11024,11025,11026,11027,11028,11029,11030,11031,11032,11033,11034,11035,11036,11037,11038,11039,11040,11041,11042,11043,11044,11045,11046,11047,11048,11049,11050,11051,11052,11053,11054,11055,11056,11057,11058,11059,11060,11061,11062,11063,11064,11065,11066,11067,11068,11069,11070,11071,11072,11073,11074,11075,11076,11077,11078,11079,11080,11081,11082,11083,11084,11085,11086,11087,11088,11089,11090,11091,11092,11094,11096,11098,11100,11102,11104,11106,11108,11110,11112,11114,11116,11118,11120,11122,11124,11126,11128,11130,11132,11134,11136,11138,11140]

def refs57 : List ℕ := [11141,11142,11143,11144,11145,11146,11147,11148,11149,11150,11151,11152,11153,11154,11155,11156,11157,11158,11159,11160,11161,11162,11163,11164,11165,11166,11167,11168,11169,11170,11171,11172,11173,11174,11175,11176,11177,11178,11179,11180,11181,11182,11183,11184,11185,11186,11187,11188,11189,11190,11191,11192,11193,11194,11195,11196,11197,11198,11199,11200,11201,11202,11203,11204,11205,11206,11207,11208,11209,11210,11211,11212,11213,11214,11215,11216,11217,11218,11219,11220,11221,11222,11223,11224,11225,11226,11227,11228,11229,11230,11231,11232,11233,11234,11235,11236,11237,11238,11239,11240,11241,11242,11243,11244,11245,11246,11247,11248,11249,11250,11251,11253,11255,11257,11259,11261,11263,11265,11267,11269,11271,11273,11275,11277,11279,11281,11283,11285,11287,11289,11291,11293,11295,11297,11299]

def refs58 : List ℕ := [11300,11301,11302,11303,11304,11305,11306,11307,11308,11309,11310,11311,11312,11313,11314,11315,11316,11317,11318,11319,11320,11321,11322,11323,11324,11325,11326,11327,11328,11329,11330,11331,11332,11333,11334,11335,11336,11337,11338,11339,11340,11341,11342,11343,11344,11345,11346,11347,11348,11349,11350,11351,11352,11353,11354,11355,11356,11357,11358,11359,11360,11361,11362,11363,11364,11365,11366,11367,11368,11369,11370,11371,11372,11373,11374,11375,11376,11377,11378,11379,11380,11381,11382,11383,11384,11385,11386,11387,11388,11389,11390,11391,11392,11393,11394,11395,11396,11397,11398,11399,11400,11401,11402,11403,11404,11405,11406,11407,11408,11409,11410,11412,11414,11416,11418,11420,11422,11424,11426,11428,11430,11432,11434,11436,11438,11440,11442,11444,11446,11448,11450,11452,11454,11456,11458]

def refs59 : List ℕ := [11459,11460,11461,11462,11463,11464,11465,11466,11467,11468,11469,11470,11471,11472,11473,11474,11475,11476,11477,11478,11479,11480,11481,11482,11483,11484,11485,11486,11487,11488,11489,11490,11491,11492,11493,11494,11495,11496,11497,11498,11499,11500,11501,11502,11503,11504,11505,11506,11507,11508,11509,11510,11511,11512,11513,11514,11515,11516,11517,11518,11519,11520,11521,11522,11523,11524,11525,11526,11527,11528,11529,11530,11531,11532,11533,11534,11535,11536,11537,11538,11539,11540,11541,11542,11543,11544,11545,11546,11547,11548,11549,11550,11551,11552,11553,11554,11555,11556,11557,11558,11559,11560,11561,11562,11563,11564,11565,11566,11567,11568,11569,11571,11573,11575,11577,11579,11581,11583,11585,11587,11589,11591,11593,11595,11597,11599,11601,11603,11605,11607,11609,11611,11613,11615,11617]

def refs60 : List ℕ := [11618,11619,11620,11621,11622,11623,11624,11625,11626,11627,11628,11629,11630,11631,11632,11633,11634,11635,11636,11637,11638,11639,11640,11641,11642,11643,11644,11645,11646,11647,11648,11649,11650,11651,11652,11653,11654,11655,11656,11657,11658,11659,11660,11661,11662,11663,11664,11665,11666,11667,11668,11669,11670,11671,11672,11673,11674,11675,11676,11677,11678,11679,11680,11681,11682,11683,11684,11685,11686,11687,11688,11689,11690,11691,11692,11693,11694,11695,11696,11697,11698,11699,11700,11701,11702,11703,11704,11705,11707,11709,11711,11713,11715,11717,11719,11721,11723,11725,11727,11729,11731,11733,11735,11737,11739,11741,11743,11745,11747,11749,11751,11753,11755,11757,11759,11761,11763,11765,11767,11769,11771,11773,11775,11777,11779,11781,11783,11785,11787,11789,11791,11793,11795,11797,11799]

def refs61 : List ℕ := [11800,11801,11802,11803,11804,11805,11806,11807,11808,11809,11810,11811,11812,11813,11814,11815,11816,11817,11818,11819,11820,11821,11822,11823,11824,11825,11826,11827,11828,11829,11830,11831,11832,11833,11834,11835,11836,11837,11838,11839,11840,11841,11842,11843,11844,11845,11846,11847,11848,11849,11850,11851,11852,11853,11854,11855,11856,11857,11858,11859,11860,11861,11862,11863,11864,11865,11866,11867,11868,11869,11870,11871,11872,11873,11874,11875,11876,11877,11878,11879,11880,11881,11882,11883,11884,11885,11886,11887,11889,11891,11893,11895,11897,11899,11901,11903,11905,11907,11909,11911,11913,11915,11917,11919,11921,11923,11925,11927,11929,11931,11933,11935,11937,11939,11941,11943,11945,11947,11949,11951,11953,11955,11957,11959,11961,11963,11965,11967,11969,11971,11973,11975,11977,11979,11981]

def refs62 : List ℕ := [11982,11983,11984,11985,11986,11987,11988,11989,11990,11991,11992,11993,11994,11995,11996,11997,11998,11999,12000,12001,12002,12003,12004,12005,12006,12007,12008,12009,12010,12011,12012,12013,12014,12015,12016,12017,12018,12019,12020,12021,12022,12023,12024,12025,12026,12027,12028,12029,12030,12031,12032,12033,12034,12035,12036,12037,12038,12039,12040,12041,12042,12043,12044,12045,12046,12047,12048,12049,12050,12051,12052,12053,12054,12055,12056,12057,12058,12059,12060,12061,12062,12063,12064,12065,12066,12067,12068,12069,12071,12073,12075,12077,12079,12081,12083,12085,12087,12089,12091,12093,12095,12097,12099,12101,12103,12105,12107,12109,12111,12113,12115,12117,12119,12121,12123,12125,12127,12129,12131,12133,12135,12137,12139,12141,12143,12145,12147,12149,12151,12153,12155,12157,12159,12161,12163]

def refs63 : List ℕ := [12164,12165,12166,12167,12168,12169,12170,12171,12172,12173,12174,12175,12176,12177,12178,12179,12180,12181,12182,12183,12184,12185,12186,12187,12188,12189,12190,12191,12192,12193,12194,12195,12196,12197,12198,12199,12200,12201,12202,12203,12204,12205,12206,12207,12208,12209,12210,12211,12212,12213,12214,12215,12216,12217,12218,12219,12220,12221,12222,12223,12224,12225,12226,12227,12228,12229,12230,12231,12232,12233,12234,12235,12236,12237,12238,12239,12240,12241,12242,12243,12244,12245,12246,12247,12248,12249,12250,12251,12253,12255,12257,12259,12261,12263,12265,12267,12269,12271,12273,12275,12277,12279,12281,12283,12285,12287,12289,12291,12293,12295,12297,12299,12301,12303,12305,12307,12309,12311,12313,12315,12317,12319,12321,12323,12325,12327,12329,12331,12333,12335,12337,12339,12341,12343,12345]

def refs64 : List ℕ := [12346,12347,12348,12349,12350,12351,12352,12353,12354,12355,12356,12357,12358,12359,12360,12361,12362,12363,12364,12365,12366,12367,12368,12369,12370,12371,12372,12373,12374,12375,12376,12377,12378,12379,12380,12381,12382,12383,12384,12385,12386,12387,12388,12389,12390,12391,12392,12393,12394,12395,12396,12397,12398,12399,12400,12401,12402,12403,12404,12405,12406,12407,12408,12409,12410,12412,12414,12416,12418,12420,12422,12424,12426,12428,12430,12432,12434,12436,12438,12440,12442,12444,12446,12448,12450,12452,12454,12456,12458,12460,12462,12464,12466,12468,12470,12472,12474,12476,12478,12480,12482,12484,12486,12488,12490,12492,12494,12496,12498,12500,12502,12504,12506,12508,12510,12512,12514,12516,12518,12520,12522,12524,12526,12528,12530,12532,12534,12536,12538,12540,12542,12544,12546,12548,12550]

def refs65 : List ℕ := [12551,12552,12553,12554,12555,12556,12557,12558,12559,12560,12561,12562,12563,12564,12565,12566,12567,12568,12569,12570,12571,12572,12573,12574,12575,12576,12577,12578,12579,12580,12581,12582,12583,12584,12585,12586,12587,12588,12589,12590,12591,12592,12593,12594,12595,12596,12597,12598,12599,12600,12601,12602,12603,12604,12605,12606,12607,12608,12609,12610,12611,12612,12613,12614,12615,12616,12617,12618,12619,12620,12621,12622,12623,12624,12625,12626,12627,12628,12629,12630,12631,12632,12633,12634,12635,12636,12637,12638,12639,12640,12641,12642,12643,12644,12645,12646,12647,12648,12649,12650,12651,12652,12653,12654,12655,12656,12657,12658,12659,12660,12661,12662,12663,12664,12665,12666,12667,12668,12669,12670,12671,12672,12673,12674,12675,12676,12677,12678,12679,12680,12681,12682,12683,12684,12685]

def refs66 : List ℕ := [12686,12687,12688,12689,12690,12691,12692,12693,12694,12695,12696,12697,12698,12699,12700,12701,12702,12703,12704,12705,12706,12707,12708,12709,12710,12711,12712,12713,12714,12715,12716,12717,12718,12719,12720,12721,12722,12723,12724,12725,12726,12727,12728,12729,12730,12731,12732,12733,12734,12735,12736,12737,12738,12739,12740,12741,12742,12743,12744,12745,12746,12747,12748,12749,12750,12751,12752,12753,12754,12755,12756,12757,12758,12759,12760,12761,12762,12763,12764,12765,12766,12767,12768,12769,12770,12771,12772,12773,12774,12775,12776,12777,12778,12779,12780,12781,12782,12783,12784,12785,12786,12787,12788,12789,12790,12791,12792,12793,12794,12795,12796,12797,12798,12799,12800,12801,12802,12803,12804,12805,12806,12807,12808,12809,12810,12811,12812,12813,12814,12815,12816,12817,12818,12819,12820]

def refs67 : List ℕ := [12821,12822,12823,12824,12825,12826,12827,12828,12829,12830,12831,12832,12833,12834,12835,12836,12837,12838,12839,12840,12841,12842,12843,12844,12845,12846,12847,12848,12849,12850,12851,12852,12853,12854,12855,12856,12857,12858,12859,12860,12861,12862,12863,12864,12865,12866,12867,12868,12869,12870,12871,12872,12873,12874,12875,12876,12877,12878,12879,12880,12881,12882,12883,12884,12885,12886,12887,12888,12889,12890,12891,12892,12893,12894,12895,12896,12897,12898,12899,12900,12901,12902,12903,12904,12905,12906,12907,12908,12909,12910,12911,12912,12913,12914,12915,12916,12917,12918,12919,12920,12921,12922,12923,12924,12925,12926,12927,12928,12929,12930,12931,12932,12933,12934,12935,12936,12937,12938,12939,12940,12941,12942,12943,12944,12945,12946,12947,12948,12949,12950,12951,12952,12953,12954,12955]

def refs68 : List ℕ := [12956,12957,12958,12959,12960,12961,12962,12963,12964,12965,12966,12967,12968,12969,12970,12971,12972,12973,12974,12975,12976,12977,12978,12979,12980,12981,12982,12983,12984,12985,12986,12987,12988,12989,12990,12991,12992,12993,12994,12995,12996,12997,12998,12999,13000,13001,13002,13003,13004,13005,13006,13007,13008,13009,13010,13011,13012,13013,13014,13015,13016,13017,13018,13019,13020,13021,13022,13023,13024,13025,13026,13027,13028,13029,13030,13031,13032,13033,13034,13035,13036,13037,13038,13039,13040,13041,13042,13043,13044,13045,13046,13047,13048,13049,13050,13051,13052,13053,13054,13055,13056,13057,13058,13059,13060,13061,13062,13063,13064,13065,13066,13067,13068,13069,13070,13071,13072,13073,13074,13075,13076,13077,13078,13079,13080,13081,13082,13083,13084,13085,13086,13087,13088,13089,13090]

def refs69 : List ℕ := [13091,13092,13093,13094,13095,13096,13097,13098,13099,13100,13101,13102,13103,13104,13105,13106,13107,13108,13109,13110,13111,13112,13113,13114,13115,13116,13117,13118,13119,13120,13121,13122,13123,13124,13125,13126,13127,13128,13129,13130,13131,13132,13133,13134,13135,13136,13137,13138,13139,13140,13141,13142,13143,13144,13145,13146,13147,13148,13149,13150,13151,13152,13153,13154,13155,13156,13157,13158,13159,13160,13161,13162,13163,13164,13165,13166,13167,13168,13169,13170,13171,13172,13173,13174,13175,13176,13177,13178,13179,13180,13181,13182,13183,13184,13185,13186,13187,13188,13189,13190,13191,13192,13193,13194,13195,13196,13197,13198,13199,13200,13201,13202,13203,13204,13205,13206,13207,13208,13209,13210,13211,13212,13213,13214,13215,13216,13217,13218,13219,13220,13221,13222,13223,13224,13225]

def refs70 : List ℕ := [13226,13227,13228,13229,13230,13231,13232,13233,13234,13235,13236,13237,13238,13239,13240,13241,13242,13243,13244,13245,13246,13247,13248,13249,13250,13251,13252,13253,13254,13255,13256,13257,13258,13259,13260,13261,13262,13263,13264,13265,13266,13267,13268,13269,13270,13271,13272,13273,13274,13275,13276,13277,13278,13279,13280,13281,13282,13283,13284,13285,13286,13287,13288,13289,13290,13291,13292,13293,13294,13295,13296,13297,13298,13299,13300,13301,13302,13303,13304,13305,13306,13307,13308,13309,13310,13311,13312,13313,13314,13315,13316,13317,13318,13319,13320,13321,13322,13323,13324,13325,13326,13327,13328,13329,13330,13331,13332,13333,13334,13335,13336,13337,13338,13339,13340,13341,13342,13343,13344,13345,13346,13347,13348,13349,13350,13351,13352,13353,13354,13355,13356,13357,13358,13359,13361]

def refs71 : List ℕ := [13362,13363,13364,13365,13366,13367,13368,13369,13370,13371,13372,13373,13374,13375,13376,13377,13378,13379,13380,13381,13382,13383,13384,13385,13386,13387,13388,13389,13390,13391,13392,13393,13394,13395,13396,13397,13398,13399,13400,13401,13402,13403,13404,13405,13406,13407,13408,13409,13410,13411,13412,13413,13414,13415,13416,13417,13418,13419,13420,13421,13422,13423,13424,13425,13426,13427,13428,13429,13430,13431,13432,13433,13434,13435,13436,13437,13438,13439,13440,13441,13442,13443,13444,13445,13446,13447,13448,13449,13450,13451,13452,13453,13454,13455,13456,13457,13458,13459,13460,13461,13462,13463,13464,13465,13466,13467,13468,13469,13470,13471,13472,13473,13474,13475,13476,13477,13478,13479,13480,13481,13482,13483,13484,13485,13486,13487,13488,13489,13490,13491,13492,13493,13494,13495,13497]

def refs72 : List ℕ := [13498,13499,13500,13501,13502,13503,13504,13505,13506,13507,13508,13509,13510,13511,13512,13513,13514,13515,13516,13517,13518,13519,13520,13521,13522,13523,13524,13525,13526,13527,13528,13529,13530,13531,13532,13533,13534,13535,13536,13537,13538,13539,13540,13541,13542,13543,13544,13545,13546,13547,13548,13549,13550,13551,13552,13553,13554,13555,13556,13557,13558,13559,13560,13561,13562,13563,13564,13565,13566,13567,13568,13569,13570,13571,13572,13573,13574,13575,13576,13577,13578,13579,13580,13581,13582,13583,13584,13585,13586,13587,13588,13589,13590,13591,13592,13593,13594,13595,13596,13597,13598,13599,13600,13601,13602,13603,13604,13605,13606,13607,13608,13609,13610,13611,13612,13613,13614,13615,13616,13617,13618,13619,13620,13621,13622,13623,13624,13625,13626,13627,13628,13629,13630,13631,13633]

def refs73 : List ℕ := [13634,13635,13636,13637,13638,13639,13640,13641,13642,13643,13644,13645,13646,13647,13648,13649,13650,13651,13652,13653,13654,13655,13656,13657,13658,13659,13660,13661,13662,13663,13664,13665,13666,13667,13668,13669,13670,13671,13672,13673,13674,13675,13676,13677,13678,13679,13680,13681,13682,13683,13684,13685,13686,13687,13688,13689,13690,13691,13692,13693,13694,13695,13696,13697,13698,13699,13700,13701,13702,13703,13704,13705,13706,13707,13708,13709,13710,13711,13712,13713,13714,13715,13716,13717,13718,13719,13720,13721,13722,13723,13724,13725,13726,13727,13728,13729,13730,13731,13732,13733,13734,13735,13736,13737,13738,13739,13740,13741,13742,13743,13744,13745,13746,13747,13748,13749,13750,13751,13752,13753,13754,13755,13756,13757,13758,13759,13760,13761,13762,13763,13764,13765,13766,13767,13769]

def refs74 : List ℕ := [13770,13771,13772,13773,13774,13775,13776,13777,13778,13779,13780,13781,13782,13783,13784,13785,13786,13787,13788,13789,13790,13791,13792,13793,13794,13795,13796,13797,13798,13799,13800,13801,13802,13803,13804,13805,13806,13807,13808,13809,13810,13811,13812,13813,13814,13815,13816,13817,13818,13819,13820,13821,13822,13823,13824,13825,13826,13827,13828,13829,13830,13831,13832,13833,13834,13835,13836,13837,13838,13839,13840,13841,13842,13843,13844,13845,13846,13847,13848,13849,13850,13851,13852,13853,13854,13855,13856,13857,13858,13859,13860,13861,13862,13863,13864,13865,13866,13867,13868,13869,13870,13871,13872,13873,13874,13875,13876,13877,13878,13879,13880,13881,13882,13883,13884,13885,13886,13887,13888,13889,13890,13891,13892,13893,13894,13895,13896,13897,13898,13899,13900,13901,13902,13903,13905]

def refs75 : List ℕ := [13906,13907,13908,13909,13910,13911,13912,13913,13914,13915,13916,13917,13918,13919,13920,13921,13922,13923,13924,13925,13926,13927,13928,13929,13930,13931,13932,13933,13934,13935,13936,13937,13938,13939,13940,13941,13942,13943,13944,13945,13946,13947,13948,13949,13950,13951,13952,13953,13954,13955,13956,13957,13958,13959,13960,13961,13962,13963,13964,13965,13966,13967,13968,13969,13970,13971,13972,13973,13974,13975,13976,13977,13978,13979,13980,13981,13982,13983,13984,13985,13986,13987,13988,13989,13990,13991,13992,13993,13994,13995,13996,13997,13998,13999,14000,14001,14002,14003,14004,14005,14006,14007,14008,14009,14010,14011,14012,14013,14014,14015,14016,14017,14018,14019,14020,14021,14022,14023,14024,14025,14026,14027,14028,14029,14030,14031,14032,14033,14034,14035,14036,14037,14038,14039,14041]

def refs76 : List ℕ := [14042,14043,14044,14045,14046,14047,14048,14049,14050,14051,14052,14053,14054,14055,14056,14057,14058,14059,14060,14061,14062,14063,14064,14065,14066,14067,14068,14069,14070,14071,14072,14073,14074,14075,14076,14077,14078,14079,14080,14081,14082,14083,14084,14085,14086,14087,14088,14089,14090,14091,14092,14093,14094,14095,14096,14097,14098,14099,14100,14101,14102,14103,14104,14105,14106,14107,14108,14109,14110,14111,14112,14113,14114,14115,14116,14117,14118,14119,14120,14121,14122,14123,14124,14125,14126,14127,14128,14129,14130,14131,14132,14133,14134,14135,14136,14137,14138,14139,14140,14141,14142,14143,14144,14145,14146,14147,14148,14149,14150,14151,14152,14153,14154,14155,14156,14157,14158,14159,14160,14161,14162,14163,14164,14165,14166,14167,14168,14170,14172,14174,14176,14178,14180,14182,14184]

def refs77 : List ℕ := [14185,14186,14187,14188,14189,14190,14191,14192,14193,14194,14195,14196,14197,14198,14199,14200,14201,14202,14203,14204,14205,14206,14207,14208,14209,14210,14211,14212,14213,14214,14215,14216,14217,14218,14219,14220,14221,14222,14223,14224,14225,14226,14227,14228,14229,14230,14231,14232,14233,14234,14235,14236,14237,14238,14239,14240,14241,14242,14243,14244,14245,14246,14247,14248,14249,14250,14251,14252,14253,14254,14255,14256,14257,14258,14259,14260,14261,14262,14263,14264,14265,14266,14267,14268,14269,14270,14271,14272,14273,14274,14275,14276,14277,14278,14279,14280,14281,14282,14283,14284,14285,14286,14287,14288,14289,14290,14291,14292,14293,14294,14295,14296,14297,14298,14299,14300,14301,14302,14303,14304,14305,14306,14307,14308,14309,14310,14311,14313,14315,14317,14319,14321,14323,14325,14327]

def refs78 : List ℕ := [14328,14329,14330,14331,14332,14333,14334,14335,14336,14337,14338,14339,14340,14341,14342,14343,14344,14345,14346,14347,14348,14349,14350,14351,14352,14353,14354,14355,14356,14357,14358,14359,14360,14361,14362,14363,14364,14365,14366,14367,14368,14369,14370,14371,14372,14373,14374,14375,14376,14377,14378,14379,14380,14381,14382,14383,14384,14385,14386,14387,14388,14389,14390,14391,14392,14393,14394,14395,14396,14397,14398,14399,14400,14401,14402,14403,14404,14405,14406,14407,14408,14409,14410,14411,14412,14413,14414,14415,14416,14417,14418,14419,14420,14421,14422,14423,14424,14425,14426,14427,14428,14429,14430,14431,14432,14433,14434,14435,14436,14437,14438,14439,14440,14441,14442,14443,14444,14445,14446,14447,14448,14449,14450,14451,14452,14453,14454,14456,14458,14460,14462,14464,14466,14468,14470]

def refs79 : List ℕ := [14471,14472,14473,14474,14475,14476,14477,14478,14479,14480,14481,14482,14483,14484,14485,14486,14487,14488,14489,14490,14491,14492,14493,14494,14495,14496,14497,14498,14499,14500,14501,14502,14503,14504,14505,14506,14507,14508,14509,14510,14511,14512,14513,14514,14515,14516,14517,14518,14519,14520,14521,14522,14523,14524,14525,14526,14527,14528,14529,14530,14531,14532,14533,14534,14535,14536,14537,14538,14539,14540,14541,14542,14543,14544,14545,14546,14547,14548,14549,14550,14551,14552,14553,14554,14555,14556,14557,14558,14559,14560,14561,14562,14563,14564,14565,14566,14567,14568,14569,14570,14571,14572,14573,14574,14575,14576,14577,14578,14579,14580,14581,14582,14583,14584,14585,14586,14587,14588,14589,14590,14591,14592,14593,14594,14595,14596,14597,14599,14601,14603,14605,14607,14609,14611,14613]

def refs80 : List ℕ := [14614,14615,14616,14617,14618,14619,14620,14621,14622,14623,14624,14625,14626,14627,14628,14629,14630,14631,14632,14633,14634,14635,14636,14637,14638,14639,14640,14641,14642,14643,14644,14645,14646,14647,14648,14649,14650,14651,14652,14653,14654,14655,14656,14657,14658,14659,14660,14661,14662,14663,14664,14665,14666,14667,14668,14669,14670,14671,14672,14673,14674,14675,14676,14677,14678,14679,14680,14681,14682,14683,14684,14685,14686,14687,14688,14689,14690,14691,14692,14693,14694,14695,14696,14697,14698,14699,14700,14701,14702,14703,14704,14705,14706,14707,14708,14709,14710,14711,14712,14713,14714,14715,14716,14717,14718,14719,14720,14721,14722,14723,14724,14725,14726,14727,14728,14729,14730,14731,14732,14733,14734,14735,14736,14737,14738,14739,14740,14742,14744,14746,14748,14750,14752,14754,14756]

def refs81 : List ℕ := [14757,14758,14759,14760,14761,14762,14763,14764,14765,14766,14767,14768,14769,14770,14771,14772,14773,14774,14775,14776,14777,14778,14779,14780,14781,14782,14783,14784,14785,14786,14787,14788,14789,14790,14791,14792,14793,14794,14795,14796,14797,14798,14799,14800,14801,14802,14803,14804,14805,14806,14807,14808,14809,14810,14811,14812,14813,14814,14815,14816,14817,14818,14819,14820,14821,14822,14823,14824,14825,14826,14827,14828,14829,14830,14831,14832,14833,14834,14835,14836,14837,14838,14839,14840,14841,14842,14843,14844,14845,14846,14847,14848,14849,14850,14851,14852,14853,14854,14855,14856,14857,14858,14859,14860,14861,14862,14863,14864,14865,14866,14867,14868,14869,14870,14871,14872,14873,14874,14875,14876,14877,14878,14879,14880,14881,14882,14883,14885,14887,14889,14891,14893,14895,14897,14899]

def refs82 : List ℕ := [14900,14901,14902,14903,14904,14905,14906,14907,14908,14909,14910,14911,14912,14913,14914,14915,14916,14917,14918,14919,14920,14921,14922,14923,14924,14925,14926,14927,14928,14929,14930,14931,14932,14933,14934,14935,14936,14937,14938,14939,14940,14941,14942,14943,14944,14945,14946,14947,14948,14949,14950,14951,14952,14953,14954,14955,14956,14957,14958,14959,14960,14961,14962,14963,14964,14965,14966,14967,14968,14969,14970,14971,14972,14973,14974,14975,14976,14977,14978,14979,14980,14981,14982,14983,14984,14985,14986,14987,14988,14989,14990,14991,14992,14993,14994,14995,14996,14997,14998,14999,15000,15001,15002,15003,15004,15005,15006,15007,15008,15009,15010,15011,15012,15013,15014,15015,15016,15017,15018,15019,15020,15021,15022,15023,15024,15025,15026,15028,15030,15032,15034,15036,15038,15040,15042]

def refs83 : List ℕ := [15043,15044,15045,15046,15047,15048,15049,15050,15051,15052,15053,15054,15055,15056,15057,15058,15059,15060,15061,15062,15063,15064,15065,15066,15067,15068,15069,15070,15071,15072,15073,15074,15075,15076,15077,15078,15079,15080,15081,15082,15083,15084,15085,15086,15087,15088,15089,15090,15091,15092,15093,15094,15095,15096,15097,15098,15099,15100,15101,15102,15103,15104,15105,15106,15107,15108,15109,15110,15111,15112,15113,15114,15115,15116,15117,15118,15119,15120,15121,15122,15123,15124,15125,15126,15127,15128,15129,15130,15131,15132,15133,15134,15135,15136,15137,15138,15139,15140,15141,15142,15143,15144,15145,15146,15147,15148,15149,15150,15151,15152,15153,15155,15157,15159,15161,15163,15165,15167,15169,15171,15173,15175,15177,15179,15181,15183,15185,15187,15189,15191,15193,15195,15197,15199,15201]

def refs84 : List ℕ := [15202,15203,15204,15205,15206,15207,15208,15209,15210,15211,15212,15213,15214,15215,15216,15217,15218,15219,15220,15221,15222,15223,15224,15225,15226,15227,15228,15229,15230,15231,15232,15233,15234,15235,15236,15237,15238,15239,15240,15241,15242,15243,15244,15245,15246,15247,15248,15249,15250,15251,15252,15253,15254,15255,15256,15257,15258,15259,15260,15261,15262,15263,15264,15265,15266,15267,15268,15269,15270,15271,15272,15273,15274,15275,15276,15277,15278,15279,15280,15281,15282,15283,15284,15285,15286,15287,15288,15289,15290,15291,15292,15293,15294,15295,15296,15297,15298,15299,15300,15301,15302,15303,15304,15305,15306,15307,15308,15309,15310,15311,15312,15314,15316,15318,15320,15322,15324,15326,15328,15330,15332,15334,15336,15338,15340,15342,15344,15346,15348,15350,15352,15354,15356,15358,15360]

def refs85 : List ℕ := [15361,15362,15363,15364,15365,15366,15367,15368,15369,15370,15371,15372,15373,15374,15375,15376,15377,15378,15379,15380,15381,15382,15383,15384,15385,15386,15387,15388,15389,15390,15391,15392,15393,15394,15395,15396,15397,15398,15399,15400,15401,15402,15403,15404,15405,15406,15407,15408,15409,15410,15411,15412,15413,15414,15415,15416,15417,15418,15419,15420,15421,15422,15423,15424,15425,15426,15427,15428,15429,15430,15431,15432,15433,15434,15435,15436,15437,15438,15439,15440,15441,15442,15443,15444,15445,15446,15447,15448,15449,15450,15451,15452,15453,15454,15455,15456,15457,15458,15459,15460,15461,15462,15463,15464,15465,15466,15467,15468,15469,15470,15471,15473,15475,15477,15479,15481,15483,15485,15487,15489,15491,15493,15495,15497,15499,15501,15503,15505,15507,15509,15511,15513,15515,15517,15519]

def refs86 : List ℕ := [15520,15521,15522,15523,15524,15525,15526,15527,15528,15529,15530,15531,15532,15533,15534,15535,15536,15537,15538,15539,15540,15541,15542,15543,15544,15545,15546,15547,15548,15549,15550,15551,15552,15553,15554,15555,15556,15557,15558,15559,15560,15561,15562,15563,15564,15565,15566,15567,15568,15569,15570,15571,15572,15573,15574,15575,15576,15577,15578,15579,15580,15581,15582,15583,15584,15585,15586,15587,15588,15589,15590,15591,15592,15593,15594,15595,15596,15597,15598,15599,15600,15601,15602,15603,15604,15605,15606,15607,15608,15609,15610,15611,15612,15613,15614,15615,15616,15617,15618,15619,15620,15621,15622,15623,15624,15625,15626,15627,15628,15629,15630,15632,15634,15636,15638,15640,15642,15644,15646,15648,15650,15652,15654,15656,15658,15660,15662,15664,15666,15668,15670,15672,15674,15676,15678]

def refs87 : List ℕ := [15679,15680,15681,15682,15683,15684,15685,15686,15687,15688,15689,15690,15691,15692,15693,15694,15695,15696,15697,15698,15699,15700,15701,15702,15703,15704,15705,15706,15707,15708,15709,15710,15711,15712,15713,15714,15715,15716,15717,15718,15719,15720,15721,15722,15723,15724,15725,15726,15727,15728,15729,15730,15731,15732,15733,15734,15735,15736,15737,15738,15739,15740,15741,15742,15743,15744,15745,15746,15747,15748,15749,15750,15751,15752,15753,15754,15755,15756,15757,15758,15759,15760,15761,15762,15763,15764,15765,15766,15768,15770,15772,15774,15776,15778,15780,15782,15784,15786,15788,15790,15792,15794,15796,15798,15800,15802,15804,15806,15808,15810,15812,15814,15816,15818,15820,15822,15824,15826,15828,15830,15832,15834,15836,15838,15840,15842,15844,15846,15848,15850,15852,15854,15856,15858,15860]

def refs88 : List ℕ := [15861,15862,15863,15864,15865,15866,15867,15868,15869,15870,15871,15872,15873,15874,15875,15876,15877,15878,15879,15880,15881,15882,15883,15884,15885,15886,15887,15888,15889,15890,15891,15892,15893,15894,15895,15896,15897,15898,15899,15900,15901,15902,15903,15904,15905,15906,15907,15908,15909,15910,15911,15912,15913,15914,15915,15916,15917,15918,15919,15920,15921,15922,15923,15924,15925,15926,15927,15928,15929,15930,15931,15932,15933,15934,15935,15936,15937,15938,15939,15940,15941,15942,15943,15944,15945,15946,15947,15948,15949,15950,15951,15952,15953,15954,15955,15956,15957,15958,15959,15960,15961,15962,15963,15964,15965,15966,15967,15968,15969,15970,15971,15972,15973,15974,15975,15976,15977,15978,15979,15980,15981,15982,15983,15984,15985,15986,15987,15988,15989,15990,15991,15992,15993,15994,15995]

def refs89 : List ℕ := [15996,15997,15998,15999,16000,16001,16002,16003,16004,16005,16006,16007,16008,16009,16010,16011,16012,16013,16014,16015,16016,16017,16018,16019,16020,16021,16022,16023,16024,16025,16026,16027,16028,16029,16030,16031,16032,16033,16034,16035,16036,16037,16038,16039,16040,16041,16042,16043,16044,16045,16046,16047,16048,16049,16050,16051,16052,16053,16054,16055,16056,16057,16058,16059,16060,16061,16062,16063,16064,16065,16066,16067,16068,16069,16070,16071,16072,16073,16074,16075,16076,16077,16078,16079,16080,16081,16082,16083,16084,16085,16086,16087,16088,16089,16090,16091,16092,16093,16094,16095,16096,16097,16098,16099,16100,16101,16102,16103,16104,16105,16106,16107,16108,16109,16110,16111,16112,16113,16114,16115,16116,16117,16118,16119,16120,16121,16122,16123,16124,16125,16126,16127,16128,16129,16130]

def refs90 : List ℕ := [16131,16132,16133,16134,16135,16136,16137,16138,16139,16140,16141,16142,16143,16144,16145,16146,16147,16148,16149,16150,16151,16152,16153,16154,16155,16156,16157,16158,16159,16160,16161,16162,16163,16164,16165,16166,16167,16168,16169,16170,16171,16172,16173,16174,16175,16176,16177,16178,16179,16180,16181,16182,16183,16184,16185,16186,16187,16188,16189,16190,16191,16192,16193,16194,16195,16196,16197,16198,16199,16200,16201,16202,16203,16204,16205,16206,16207,16208,16209,16210,16211,16212,16213,16214,16215,16216,16217,16218,16219,16220,16221,16222,16223,16224,16225,16226,16227,16228,16229,16230,16231,16232,16233,16234,16235,16236,16237,16238,16239,16240,16241,16242,16243,16244,16245,16246,16247,16248,16249,16250,16251,16252,16253,16254,16255,16256,16257,16258,16259,16260,16261,16262,16263,16264,16265]

def refs91 : List ℕ := [16266,16267,16268,16269,16270,16271,16272,16273,16274,16275,16276,16277,16278,16279,16280,16281,16282,16283,16284,16285,16286,16287,16288,16289,16290,16291,16292,16293,16294,16295,16296,16297,16298,16299,16300,16301,16302,16303,16304,16305,16306,16307,16308,16309,16310,16311,16312,16313,16314,16315,16316,16317,16318,16319,16320,16321,16322,16323,16324,16325,16326,16327,16328,16329,16330,16331,16332,16333,16334,16335,16336,16337,16338,16339,16340,16341,16342,16343,16344,16345,16346,16347,16348,16349,16350,16351,16352,16353,16354,16355,16356,16357,16358,16359,16360,16361,16362,16363,16364,16365,16366,16367,16368,16369,16370,16371,16372,16373,16374,16375,16376,16377,16378,16379,16380,16381,16382,16383,16384,16385,16386,16387,16388,16389,16390,16391,16392,16393,16394,16395,16396,16397,16398,16399,16400]

def refs92 : List ℕ := [16401,16402,16403,16404,16405,16406,16407,16408,16409,16410,16411,16412,16413,16414,16415,16416,16417,16418,16419,16420,16421,16422,16423,16424,16425,16426,16427,16428,16429,16430,16431,16432,16433,16434,16435,16436,16437,16438,16439,16440,16441,16442,16443,16444,16445,16446,16447,16448,16449,16450,16451,16452,16453,16454,16455,16456,16457,16458,16459,16460,16461,16462,16463,16464,16465,16466,16467,16468,16469,16470,16471,16472,16473,16474,16475,16476,16477,16478,16479,16480,16481,16482,16483,16484,16485,16486,16487,16488,16489,16490,16491,16492,16493,16494,16495,16496,16497,16498,16499,16500,16501,16502,16503,16504,16505,16506,16507,16508,16509,16510,16511,16512,16513,16514,16515,16516,16517,16518,16519,16520,16521,16522,16523,16524,16525,16526,16527,16528,16529,16530,16531,16532,16533,16534,16535]

def refs93 : List ℕ := [16536,16537,16538,16539,16540,16541,16542,16543,16544,16545,16546,16547,16548,16549,16550,16551,16552,16553,16554,16555,16556,16557,16558,16559,16560,16561,16562,16563,16564,16565,16566,16567,16568,16569,16570,16571,16572,16573,16574,16575,16576,16577,16578,16579,16580,16581,16582,16583,16584,16585,16586,16587,16588,16589,16590,16591,16592,16593,16594,16595,16596,16597,16598,16599,16600,16601,16602,16603,16604,16605,16606,16607,16608,16609,16610,16611,16612,16613,16614,16615,16616,16617,16618,16619,16620,16621,16622,16623,16624,16625,16626,16627,16628,16629,16630,16631,16632,16633,16634,16635,16636,16637,16638,16639,16640,16641,16642,16643,16644,16645,16646,16647,16648,16649,16650,16651,16652,16653,16654,16655,16656,16657,16658,16659,16660,16661,16662,16663,16664,16665,16666,16667,16668,16669,16670]

def refs94 : List ℕ := [16671,16672,16673,16674,16675,16676,16677,16678,16679,16680,16681,16682,16683,16684,16685,16686,16687,16688,16689,16690,16691,16692,16693,16694,16695,16696,16697,16698,16699,16700,16701,16702,16703,16704,16705,16706,16707,16708,16709,16710,16711,16712,16713,16714,16715,16716,16717,16718,16719,16720,16721,16722,16723,16724,16725,16726,16727,16728,16729,16730,16731,16732,16733,16734,16735,16736,16737,16738,16739,16740,16741,16742,16743,16744,16745,16746,16747,16748,16749,16750,16751,16752,16753,16754,16755,16756,16757,16758,16759,16760,16761,16762,16763,16764,16765,16766,16767,16768,16769,16770,16771,16772,16773,16774,16775,16776,16777,16778,16779,16780,16781,16782,16783,16784,16785,16786,16787,16788,16789,16790,16791,16792,16793,16794,16795,16796,16797,16798,16799,16800,16801,16802,16803,16804,16805]

def refs95 : List ℕ := [16806,16807,16808,16809,16810,16811,16812,16813,16814,16815,16816,16817,16818,16819,16820,16821,16822,16823,16824,16825,16826,16827,16828,16829,16830,16831,16832,16833,16834,16835,16836,16837,16838,16839,16840,16841,16842,16843,16844,16845,16846,16847,16848,16849,16850,16851,16852,16853,16854,16855,16856,16857,16858,16859,16860,16861,16862,16863,16864,16865,16866,16867,16868,16869,16870,16871,16872,16873,16874,16875,16876,16877,16878,16879,16880,16881,16882,16883,16884,16885,16886,16887,16888,16889,16890,16891,16892,16893,16894,16895,16896,16897,16898,16899,16900,16901,16902,16903,16904,16905,16906,16907,16908,16909,16910,16911,16912,16913,16914,16915,16916,16917,16918,16919,16920,16921,16922,16923,16924,16925,16926,16927,16928,16929,16930,16931,16932,16933,16934,16935,16936,16937,16938,16939,16940]

def refs96 : List ℕ := [16941,16942,16943,16944,16945,16946,16947,16948,16949,16950,16951,16952,16953,16954,16955,16956,16957,16958,16959,16960,16961,16962,16963,16964,16965,16966,16967,16968,16969,16970,16971,16972,16973,16974,16975,16976,16977,16978,16979,16980,16981,16982,16983,16984,16985,16986,16987,16988,16989,16990,16991,16992,16993,16994,16995,16996,16997,16998,16999,17000,17001,17002,17003,17004,17005,17006,17007,17008,17009,17010,17011,17012,17013,17014,17015,17016,17017,17018,17019,17020,17021,17022,17023,17024,17025,17026,17027,17028,17029,17030,17031,17032,17033,17034,17035,17036,17037,17038,17039,17040,17041,17042,17043,17044,17045,17046,17047,17048,17049,17050,17051,17052,17053,17054,17055,17056,17057,17058,17059,17060,17061,17062,17063,17064,17065,17066,17067,17068,17069,17070,17071,17072,17073,17074,17075]

def refs97 : List ℕ := [17076,17077,17078,17079,17080,17081,17082,17083,17084,17085,17086,17087,17088,17089,17090,17091,17092,17093,17094,17095,17096,17097,17098,17099,17100,17101,17102,17103,17104,17105,17106,17107,17108,17109,17110,17111,17112,17113,17114,17115,17116,17117,17118,17119,17120,17121,17122,17123,17124,17125,17126,17127,17128,17129,17130,17131,17132,17133,17134,17135,17136,17137,17138,17139,17140,17141,17142,17143,17144,17145,17146,17147,17148,17149,17150,17151,17152,17153,17154,17155,17156,17157,17158,17159,17160,17161,17162,17163,17164,17165,17166,17167,17168,17169,17170,17171,17172,17173,17174,17175,17176,17177,17178,17179,17180,17181,17182,17183,17184,17185,17186,17187,17188,17189,17190,17191,17192,17193,17194,17195,17196,17197,17198,17199,17200,17201,17202,17203,17204,17205,17206,17207,17208,17209,17211]

def refs98 : List ℕ := [17212,17213,17214,17215,17216,17217,17218,17219,17220,17221,17222,17223,17224,17225,17226,17227,17228,17229,17230,17231,17232,17233,17234,17235,17236,17237,17238,17239,17240,17241,17242,17243,17244,17245,17246,17247,17248,17249,17250,17251,17252,17253,17254,17255,17256,17257,17258,17259,17260,17261,17262,17263,17264,17265,17266,17267,17268,17269,17270,17271,17272,17273,17274,17275,17276,17277,17278,17279,17280,17281,17282,17283,17284,17285,17286,17287,17288,17289,17290,17291,17292,17293,17294,17295,17296,17297,17298,17299,17300,17301,17302,17303,17304,17305,17306,17307,17308,17309,17310,17311,17312,17313,17314,17315,17316,17317,17318,17319,17320,17321,17322,17323,17324,17325,17326,17327,17328,17329,17330,17331,17332,17333,17334,17335,17336,17337,17338,17339,17340,17341,17342,17343,17344,17345,17347]

def refs99 : List ℕ := [17348,17349,17350,17351,17352,17353,17354,17355,17356,17357,17358,17359,17360,17361,17362,17363,17364,17365,17366,17367,17368,17369,17370,17371,17372,17373,17374,17375,17376,17377,17378,17379,17380,17381,17382,17383,17384,17385,17386,17387,17388,17389,17390,17391,17392,17393,17394,17395,17396,17397,17398,17399,17400,17401,17402,17403,17404,17405,17406,17407,17408,17409,17410,17411,17412,17413,17414,17415,17416,17417,17418,17419,17420,17421,17422,17423,17424,17425,17426,17427,17428,17429,17430,17431,17432,17433,17434,17435,17436,17437,17438,17439,17440,17441,17442,17443,17444,17445,17446,17447,17448,17449,17450,17451,17452,17453,17454,17455,17456,17457,17458,17459,17460,17461,17462,17463,17464,17465,17466,17467,17468,17469,17470,17471,17472,17473,17474,17475,17476,17477,17478,17479,17480,17481,17483]

def refs100 : List ℕ := [17484,17485,17486,17487,17488,17489,17490,17491,17492,17493,17494,17495,17496,17497,17498,17499,17500,17501,17502,17503,17504,17505,17506,17507,17508,17509,17510,17511,17512,17513,17514,17515,17516,17517,17518,17519,17520,17521,17522,17523,17524,17525,17526,17527,17528,17529,17530,17531,17532,17533,17534,17535,17536,17537,17538,17539,17540,17541,17542,17543,17544,17545,17546,17547,17548,17549,17550,17551,17552,17553,17554,17555,17556,17557,17558,17559,17560,17561,17562,17563,17564,17565,17566,17567,17568,17569,17570,17571,17572,17573,17574,17575,17576,17577,17578,17579,17580,17581,17582,17583,17584,17585,17586,17587,17588,17589,17590,17591,17592,17593,17594,17595,17596,17597,17598,17599,17600,17601,17602,17603,17604,17605,17606,17607,17608,17609,17610,17611,17612,17613,17614,17615,17616,17617,17619]

def refs101 : List ℕ := [17620,17621,17622,17623,17624,17625,17626,17627,17628,17629,17630,17631,17632,17633,17634,17635,17636,17637,17638,17639,17640,17641,17642,17643,17644,17645,17646,17647,17648,17649,17650,17651,17652,17653,17654,17655,17656,17657,17658,17659,17660,17661,17662,17663,17664,17665,17666,17667,17668,17669,17670,17671,17672,17673,17674,17675,17676,17677,17678,17679,17680,17681,17682,17683,17684,17685,17686,17687,17688,17689,17690,17691,17692,17693,17694,17695,17696,17697,17698,17699,17700,17701,17702,17703,17704,17705,17706,17707,17708,17709,17710,17711,17712,17713,17714,17715,17716,17717,17718,17719,17720,17721,17722,17723,17724,17725,17726,17727,17728,17729,17730,17731,17732,17733,17734,17735,17736,17737,17738,17739,17740,17741,17742,17743,17744,17745,17746,17747,17748,17749,17750,17751,17752,17753,17755]

def refs102 : List ℕ := [17756,17757,17758,17759,17760,17761,17762,17763,17764,17765,17766,17767,17768,17769,17770,17771,17772,17773,17774,17775,17776,17777,17778,17779,17780,17781,17782,17783,17784,17785,17786,17787,17788,17789,17790,17791,17792,17793,17794,17795,17796,17797,17798,17799,17800,17801,17802,17803,17804,17805,17806,17807,17808,17809,17810,17811,17812,17813,17814,17815,17816,17817,17818,17819,17820,17821,17822,17823,17824,17825,17826,17827,17828,17829,17830,17831,17832,17833,17834,17835,17836,17837,17838,17839,17840,17841,17842,17843,17844,17845,17846,17847,17848,17849,17850,17851,17852,17853,17854,17855,17856,17857,17858,17859,17860,17861,17862,17863,17864,17865,17866,17867,17868,17869,17870,17871,17872,17873,17874,17875,17876,17877,17878,17879,17880,17881,17882,17883,17884,17885,17886,17887,17888,17889,17891]

def refs103 : List ℕ := [17892,17893,17894,17895,17896,17897,17898,17899,17900,17901,17902,17903,17904,17905,17906,17907,17908,17909,17910,17911,17912,17913,17914,17915,17916,17917,17918,17919,17920,17921,17922,17923,17924,17925,17926,17927,17928,17929,17930,17931,17932,17933,17934,17935,17936,17937,17938,17939,17940,17941,17942,17943,17944,17945,17946,17947,17948,17949,17950,17951,17952,17953,17954,17955,17956,17957,17958,17959,17960,17961,17962,17963,17964,17965,17966,17967,17968,17969,17970,17971,17972,17973,17974,17975,17976,17977,17978,17979,17980,17981,17982,17983,17984,17985,17986,17987,17988,17989,17990,17991,17992,17993,17994,17995,17996,17997,17998,17999,18000,18001,18002,18003,18004,18005,18006,18007,18008,18009,18010,18011,18012,18013,18014,18015,18016,18017,18018,18019,18020,18021,18022,18023,18024,18025,18027]

def refs104 : List ℕ := [18028,18029,18030,18031,18032,18033,18034,18035,18036,18037,18038,18039,18040,18041,18042,18043,18044,18045,18046,18047,18048,18049,18050,18051,18052,18053,18054,18055,18056,18057,18058,18059,18060,18061,18062,18063,18064,18065,18066,18067,18068,18069,18070,18071,18072,18073,18074,18075,18076,18077,18078,18079,18080,18081,18082,18083,18084,18085,18086,18087,18088,18089,18090,18091,18092,18093,18094,18095,18096,18097,18098,18099,18100,18101,18102,18103,18104,18105,18106,18107,18108,18109,18110,18111,18112,18113,18114,18115,18116,18117,18118,18119,18120,18121,18122,18123,18124,18125,18126,18127,18128,18129,18130,18131,18132,18133,18134,18135,18136,18137,18138,18139,18140,18141,18142,18143,18144,18145,18146,18147,18148,18149,18150,18151,18152,18153,18154,18155,18156,18157,18158,18159,18160,18161,18163]

def refs105 : List ℕ := [18164,18165,18166,18167,18168,18169,18170,18171,18172,18173,18174,18175,18176,18177,18178,18179,18180,18181,18182,18183,18184,18185,18186,18187,18188,18189,18190,18191,18192,18193,18194,18195,18196,18197,18198,18199,18200,18201,18202,18203,18204,18205,18206,18207,18208,18209,18210,18211,18212,18213,18214,18215,18216,18217,18218,18219,18220,18221,18222,18223,18224,18225,18226,18227,18228,18229,18230,18231,18232,18233,18234,18235,18236,18237,18238,18239,18240,18241,18242,18243,18244,18245,18246,18247,18248,18249,18250,18251,18252,18253,18254,18255,18256,18257,18258,18259,18260,18261,18262,18263,18264,18265,18266,18267,18268,18269,18270,18271,18272,18273,18274,18275,18276,18277,18278,18279,18280,18281,18282,18283,18284,18285,18286,18287,18288,18289,18290,18292,18294,18296,18298,18300,18302,18304,18306]

def refs106 : List ℕ := [18307,18308,18309,18310,18311,18312,18313,18314,18315,18316,18317,18318,18319,18320,18321,18322,18323,18324,18325,18326,18327,18328,18329,18330,18331,18332,18333,18334,18335,18336,18337,18338,18339,18340,18341,18342,18343,18344,18345,18346,18347,18348,18349,18350,18351,18352,18353,18354,18355,18356,18357,18358,18359,18360,18361,18362,18363,18364,18365,18366,18367,18368,18369,18370,18371,18372,18373,18374,18375,18376,18377,18378,18379,18380,18381,18382,18383,18384,18385,18386,18387,18388,18389,18390,18391,18392,18393,18394,18395,18396,18397,18398,18399,18400,18401,18402,18403,18404,18405,18406,18407,18408,18409,18410,18411,18412,18413,18414,18415,18416,18417,18418,18419,18420,18421,18422,18423,18424,18425,18426,18427,18428,18429,18430,18431,18432,18433,18435,18437,18439,18441,18443,18445,18447,18449]

def refs107 : List ℕ := [18450,18451,18452,18453,18454,18455,18456,18457,18458,18459,18460,18461,18462,18463,18464,18465,18466,18467,18468,18469,18470,18471,18472,18473,18474,18475,18476,18477,18478,18479,18480,18481,18482,18483,18484,18485,18486,18487,18488,18489,18490,18491,18492,18493,18494,18495,18496,18497,18498,18499,18500,18501,18502,18503,18504,18505,18506,18507,18508,18509,18510,18511,18512,18513,18514,18515,18516,18517,18518,18519,18520,18521,18522,18523,18524,18525,18526,18527,18528,18529,18530,18531,18532,18533,18534,18535,18536,18537,18538,18539,18540,18541,18542,18543,18544,18545,18546,18547,18548,18549,18550,18551,18552,18553,18554,18555,18556,18557,18558,18559,18560,18561,18562,18563,18564,18565,18566,18567,18568,18569,18570,18571,18572,18573,18574,18575,18576,18578,18580,18582,18584,18586,18588,18590,18592]

def refs108 : List ℕ := [18593,18594,18595,18596,18597,18598,18599,18600,18601,18602,18603,18604,18605,18606,18607,18608,18609,18610,18611,18612,18613,18614,18615,18616,18617,18618,18619,18620,18621,18622,18623,18624,18625,18626,18627,18628,18629,18630,18631,18632,18633,18634,18635,18636,18637,18638,18639,18640,18641,18642,18643,18644,18645,18646,18647,18648,18649,18650,18651,18652,18653,18654,18655,18656,18657,18658,18659,18660,18661,18662,18663,18664,18665,18666,18667,18668,18669,18670,18671,18672,18673,18674,18675,18676,18677,18678,18679,18680,18681,18682,18683,18684,18685,18686,18687,18688,18689,18690,18691,18692,18693,18694,18695,18696,18697,18698,18699,18700,18701,18702,18703,18704,18705,18706,18707,18708,18709,18710,18711,18712,18713,18714,18715,18716,18717,18718,18719,18721,18723,18725,18727,18729,18731,18733,18735]

def refs109 : List ℕ := [18736,18737,18738,18739,18740,18741,18742,18743,18744,18745,18746,18747,18748,18749,18750,18751,18752,18753,18754,18755,18756,18757,18758,18759,18760,18761,18762,18763,18764,18765,18766,18767,18768,18769,18770,18771,18772,18773,18774,18775,18776,18777,18778,18779,18780,18781,18782,18783,18784,18785,18786,18787,18788,18789,18790,18791,18792,18793,18794,18795,18796,18797,18798,18799,18800,18801,18802,18803,18804,18805,18806,18807,18808,18809,18810,18811,18812,18813,18814,18815,18816,18817,18818,18819,18820,18821,18822,18823,18824,18825,18826,18827,18828,18829,18830,18831,18832,18833,18834,18835,18836,18837,18838,18839,18840,18841,18842,18843,18844,18845,18846,18847,18848,18849,18850,18851,18852,18853,18854,18855,18856,18857,18858,18859,18860,18861,18862,18864,18866,18868,18870,18872,18874,18876,18878]

def refs110 : List ℕ := [18879,18880,18881,18882,18883,18884,18885,18886,18887,18888,18889,18890,18891,18892,18893,18894,18895,18896,18897,18898,18899,18900,18901,18902,18903,18904,18905,18906,18907,18908,18909,18910,18911,18912,18913,18914,18915,18916,18917,18918,18919,18920,18921,18922,18923,18924,18925,18926,18927,18928,18929,18930,18931,18932,18933,18934,18935,18936,18937,18938,18939,18940,18941,18942,18943,18944,18945,18946,18947,18948,18949,18950,18951,18952,18953,18954,18955,18956,18957,18958,18959,18960,18961,18962,18963,18964,18965,18966,18967,18968,18969,18970,18971,18972,18973,18974,18975,18976,18977,18978,18979,18980,18981,18982,18983,18984,18985,18986,18987,18988,18989,18991,18993,18995,18997,18999,19001,19003,19005,19007,19009,19011,19013,19015,19017,19019,19021,19023,19025,19027,19029,19031,19033,19035,19037]

def refs111 : List ℕ := [19038,19039,19040,19041,19042,19043,19044,19045,19046,19047,19048,19049,19050,19051,19052,19053,19054,19055,19056,19057,19058,19059,19060,19061,19062,19063,19064,19065,19066,19067,19068,19069,19070,19071,19072,19073,19074,19075,19076,19077,19078,19079,19080,19081,19082,19083,19084,19085,19086,19087,19088,19089,19090,19091,19092,19093,19094,19095,19096,19097,19098,19099,19100,19101,19102,19103,19104,19105,19106,19107,19108,19109,19110,19111,19112,19113,19114,19115,19116,19117,19118,19119,19120,19121,19122,19123,19124,19125,19126,19127,19128,19129,19130,19131,19132,19133,19134,19135,19136,19137,19138,19139,19140,19141,19142,19143,19144,19145,19146,19147,19148,19149,19150,19151,19152,19153,19154,19155,19156,19157,19158,19159,19160,19161,19162,19163,19164,19165,19166,19167,19168,19169,19170,19171,19172]

def refs112 : List ℕ := [19173,19174,19175,19176,19177,19178,19179,19180,19181,19182,19183,19184,19185,19186,19187,19188,19189,19190,19191,19192,19193,19194,19195,19196,19197,19198,19199,19200,19201,19202,19203,19204,19205,19206,19207,19208,19209,19210,19211,19212,19213,19214,19215,19216,19217,19218,19219,19220,19221,19222,19223,19224,19225,19226,19227,19228,19229,19230,19231,19232,19233,19234,19235,19236,19237,19238,19239,19240,19241,19242,19243,19244,19245,19246,19247,19248,19249,19250,19251,19252,19253,19254,19255,19256,19257,19258,19259,19260,19261,19262,19263,19264,19265,19266,19267,19268,19269,19270,19271,19272,19273,19274,19275,19276,19277,19278,19279,19280,19281,19282,19283,19284,19285,19286,19287,19288,19289,19290,19291,19292,19293,19294,19295,19296,19297,19298,19299,19300,19301,19302,19303,19304,19305,19306,19307]

def refs113 : List ℕ := [19308,19309,19310,19311,19312,19313,19314,19315,19316,19317,19318,19319,19320,19321,19322,19323,19324,19325,19326,19327,19328,19329,19330,19331,19332,19333,19334,19335,19336,19337,19338,19339,19340,19341,19342,19343,19344,19345,19346,19347,19348,19349,19350,19351,19352,19353,19354,19355,19356,19357,19358,19359,19360,19361,19362,19363,19364,19365,19366,19367,19368,19369,19370,19371,19372,19373,19374,19375,19376,19377,19378,19379,19380,19381,19382,19383,19384,19385,19386,19387,19388,19389,19390,19391,19392,19393,19394,19395,19396,19397,19398,19399,19400,19401,19402,19403,19404,19405,19406,19407,19408,19409,19410,19411,19412,19413,19414,19415,19416,19417,19418,19419,19420,19421,19422,19423,19424,19425,19426,19427,19428,19429,19430,19431,19432,19433,19434,19435,19436,19437,19438,19439,19440,19441,19442]

def refs114 : List ℕ := [19443,19444,19445,19446,19447,19448,19449,19450,19451,19452,19453,19454,19455,19456,19457,19458,19459,19460,19461,19462,19463,19464,19465,19466,19467,19468,19469,19470,19471,19472,19473,19474,19475,19476,19477,19478,19479,19480,19481,19482,19483,19484,19485,19486,19487,19488,19489,19490,19491,19492,19493,19494,19495,19496,19497,19498,19499,19500,19501,19502,19503,19504,19505,19506,19507,19508,19509,19510,19511,19512,19513,19514,19515,19516,19517,19518,19519,19520,19521,19522,19523,19524,19525,19526,19527,19528,19529,19530,19531,19532,19533,19534,19535,19536,19537,19538,19539,19540,19541,19542,19543,19544,19545,19546,19547,19548,19549,19550,19551,19552,19553,19554,19555,19556,19557,19558,19559,19560,19561,19562,19563,19564,19565,19566,19567,19568,19569,19570,19571,19572,19573,19574,19575,19576,19577]

def refs115 : List ℕ := [19578,19579,19580,19581,19582,19583,19584,19585,19586,19587,19588,19589,19590,19591,19592,19593,19594,19595,19596,19597,19598,19599,19600,19601,19602,19603,19604,19605,19606,19607,19608,19609,19610,19611,19612,19613,19614,19615,19616,19617,19618,19619,19620,19621,19622,19623,19624,19625,19626,19627,19628,19629,19630,19631,19632,19633,19634,19635,19636,19637,19638,19639,19640,19641,19642,19643,19644,19645,19646,19647,19648,19649,19650,19651,19652,19653,19654,19655,19656,19657,19658,19659,19660,19661,19662,19663,19664,19665,19666,19667,19668,19669,19670,19671,19672,19673,19674,19675,19676,19677,19678,19679,19680,19681,19682,19683,19684,19685,19686,19687,19688,19689,19690,19691,19692,19693,19694,19695,19696,19697,19698,19699,19700,19701,19702,19703,19704,19705,19706,19707,19708,19709,19710,19711,19712]

def refs116 : List ℕ := [19713,19714,19715,19716,19717,19718,19719,19720,19721,19722,19723,19724,19725,19726,19727,19728,19729,19730,19731,19732,19733,19734,19735,19736,19737,19738,19739,19740,19741,19742,19743,19744,19745,19746,19747,19748,19749,19750,19751,19752,19753,19754,19755,19756,19757,19758,19759,19760,19761,19762,19763,19764,19765,19766,19767,19768,19769,19770,19771,19772,19773,19774,19775,19776,19777,19778,19779,19780,19781,19782,19783,19784,19785,19786,19787,19788,19789,19790,19791,19792,19793,19794,19795,19796,19797,19798,19799,19800,19801,19802,19803,19804,19805,19806,19807,19808,19809,19810,19811,19812,19813,19814,19815,19816,19817,19818,19819,19820,19821,19822,19823,19824,19825,19826,19827,19828,19829,19830,19831,19832,19833,19834,19835,19836,19837,19838,19839,19840,19841,19842,19843,19844,19845,19846,19847]

def refs117 : List ℕ := [19848,19849,19850,19851,19852,19853,19854,19855,19856,19857,19858,19859,19860,19861,19862,19863,19864,19865,19866,19867,19868,19869,19870,19871,19872,19873,19874,19875,19876,19877,19878,19879,19880,19881,19882,19883,19884,19885,19886,19887,19888,19889,19890,19891,19892,19893,19894,19895,19896,19897,19898,19899,19900,19901,19902,19903,19904,19905,19906,19907,19908,19909,19910,19911,19912,19913,19914,19915,19916,19917,19918,19919,19920,19921,19922,19923,19924,19925,19926,19927,19928,19929,19930,19931,19932,19933,19934,19935,19936,19937,19938,19939,19940,19941,19942,19943,19944,19945,19946,19947,19948,19949,19950,19951,19952,19953,19954,19955,19956,19957,19958,19959,19960,19961,19962,19963,19964,19965,19966,19967,19968,19969,19970,19971,19972,19973,19974,19975,19976,19977,19978,19979,19980,19981,19982]

def refs118 : List ℕ := [19983,19984,19985,19986,19987,19988,19989,19990,19991,19992,19993,19994,19995,19996,19997,19998,19999,20000,20001,20002,20003,20004,20005,20006,20007,20008,20009,20010,20011,20012,20013,20014,20015,20016,20017,20018,20019,20020,20021,20022,20023,20024,20025,20026,20027,20028,20029,20030,20031,20032,20033,20034,20035,20036,20037,20038,20039,20040,20041,20042,20043,20044,20045,20046,20047,20048,20049,20050,20051,20052,20053,20054,20055,20056,20057,20058,20059,20060,20061,20062,20063,20064,20065,20066,20067,20068,20069,20070,20071,20072,20073,20074,20075,20076,20077,20078,20079,20080,20081,20082,20083,20084,20085,20086,20087,20088,20089,20090,20091,20092,20093,20094,20095,20096,20097,20098,20099,20100,20101,20102,20103,20104,20105,20106,20107,20108,20109,20110,20111,20112,20113,20114,20115,20116,20117]

def refs119 : List ℕ := [20118,20119,20120,20121,20122,20123,20124,20125,20126,20127,20128,20129,20130,20131,20132,20133,20134,20135,20136,20137,20138,20139,20140,20141,20142,20143,20144,20145,20146,20147,20148,20149,20150,20151,20152,20153,20154,20155,20156,20157,20158,20159,20160,20161,20162,20163,20164,20165,20166,20167,20168,20169,20170,20171,20172,20173,20174,20175,20176,20177,20178,20179,20180,20181,20182,20183,20184,20185,20186,20187,20188,20189,20190,20191,20192,20193,20194,20195,20196,20197,20198,20199,20200,20201,20202,20203,20204,20205,20206,20207,20208,20209,20210,20211,20212,20213,20214,20215,20216,20217,20218,20219,20220,20221,20222,20223,20224,20225,20226,20227,20228,20229,20230,20231,20232,20233,20234,20235,20236,20237,20238,20239,20240,20241,20242,20243,20244,20245,20246,20247,20248,20249,20250,20251,20252]

def refs120 : List ℕ := [20253,20254,20255,20256,20257,20258,20259,20260,20261,20262,20263,20264,20265,20266,20267,20268,20269,20270,20271,20272,20273,20274,20275,20276,20277,20278,20279,20280,20281,20282,20283,20284,20285,20286,20287,20288,20289,20290,20291,20292,20293,20294,20295,20296,20297,20298,20299,20300,20301,20302,20303,20304,20305,20306,20307,20308,20309,20310,20311,20312,20313,20314,20315,20316,20317,20318,20319,20320,20321,20322,20323,20324,20325,20326,20327,20328,20329,20330,20331,20332,20333,20334,20335,20336,20337,20338,20339,20340,20341,20342,20343,20344,20345,20346,20347,20348,20349,20350,20351,20352,20353,20354,20355,20356,20357,20358,20359,20360,20361,20362,20363,20364,20365,20366,20367,20368,20369,20370,20371,20372,20373,20374,20375,20376,20377,20378,20379,20380,20381,20382,20383,20384,20385,20386,20387]

def refs121 : List ℕ := [20388,20389,20390,20391,20392,20393,20394,20395,20396,20397,20398,20399,20400,20401,20402,20403,20404,20405,20406,20407,20408,20409,20410,20411,20412,20413,20414,20415,20416,20417,20418,20419,20420,20421,20422,20423,20424,20425,20426,20427,20428,20429,20430,20431,20432,20433,20434,20435,20436,20437,20438,20439,20440,20441,20442,20443,20444,20445,20446,20447,20448,20449,20450,20451,20452,20453,20454,20455,20456,20457,20458,20459,20460,20461,20462,20463,20464,20465,20466,20467,20468,20469,20470,20471,20472,20473,20474,20475,20476,20477,20478,20479,20480,20481,20482,20483,20484,20485,20486,20487,20488,20489,20490,20491,20492,20493,20494,20495,20496,20497,20498,20499,20500,20501,20502,20503,20504,20505,20506,20507,20508,20509,20510,20511,20512,20513,20514,20515,20516,20517,20518,20519,20520,20521,20523]

def refs122 : List ℕ := [20524,20525,20526,20527,20528,20529,20530,20531,20532,20533,20534,20535,20536,20537,20538,20539,20540,20541,20542,20543,20544,20545,20546,20547,20548,20549,20550,20551,20552,20553,20554,20555,20556,20557,20558,20559,20560,20561,20562,20563,20564,20565,20566,20567,20568,20569,20570,20571,20572,20573,20574,20575,20576,20577,20578,20579,20580,20581,20582,20583,20584,20585,20586,20587,20588,20589,20590,20591,20592,20593,20594,20595,20596,20597,20598,20599,20600,20601,20602,20603,20604,20605,20606,20607,20608,20609,20610,20611,20612,20613,20614,20615,20616,20617,20618,20619,20620,20621,20622,20623,20624,20625,20626,20627,20628,20629,20630,20631,20632,20633,20634,20635,20636,20637,20638,20639,20640,20641,20642,20643,20644,20645,20646,20647,20648,20649,20650,20651,20652,20653,20654,20655,20656,20657,20659]

def refs123 : List ℕ := [20660,20661,20662,20663,20664,20665,20666,20667,20668,20669,20670,20671,20672,20673,20674,20675,20676,20677,20678,20679,20680,20681,20682,20683,20684,20685,20686,20687,20688,20689,20690,20691,20692,20693,20694,20695,20696,20697,20698,20699,20700,20701,20702,20703,20704,20705,20706,20707,20708,20709,20710,20711,20712,20713,20714,20715,20716,20717,20718,20719,20720,20721,20722,20723,20724,20725,20726,20727,20728,20729,20730,20731,20732,20733,20734,20735,20736,20737,20738,20739,20740,20741,20742,20743,20744,20745,20746,20747,20748,20749,20750,20751,20752,20753,20754,20755,20756,20757,20758,20759,20760,20761,20762,20763,20764,20765,20766,20767,20768,20769,20770,20771,20772,20773,20774,20775,20776,20777,20778,20779,20780,20781,20782,20783,20784,20785,20786,20787,20788,20789,20790,20791,20792,20793,20795]

def refs124 : List ℕ := [20796,20797,20798,20799,20800,20801,20802,20803,20804,20805,20806,20807,20808,20809,20810,20811,20812,20813,20814,20815,20816,20817,20818,20819,20820,20821,20822,20823,20824,20825,20826,20827,20828,20829,20830,20831,20832,20833,20834,20835,20836,20837,20838,20839,20840,20841,20842,20843,20844,20845,20846,20847,20848,20849,20850,20851,20852,20853,20854,20855,20856,20857,20858,20859,20860,20861,20862,20863,20864,20865,20866,20867,20868,20869,20870,20871,20872,20873,20874,20875,20876,20877,20878,20879,20880,20881,20882,20883,20884,20885,20886,20887,20888,20889,20890,20891,20892,20893,20894,20895,20896,20897,20898,20899,20900,20901,20902,20903,20904,20905,20906,20907,20908,20909,20910,20911,20912,20913,20914,20915,20916,20917,20918,20919,20920,20921,20922,20923,20924,20925,20926,20927,20928,20929,20931]

def refs125 : List ℕ := [20932,20933,20934,20935,20936,20937,20938,20939,20940,20941,20942,20943,20944,20945,20946,20947,20948,20949,20950,20951,20952,20953,20954,20955,20956,20957,20958,20959,20960,20961,20962,20963,20964,20965,20966,20967,20968,20969,20970,20971,20972,20973,20974,20975,20976,20977,20978,20979,20980,20981,20982,20983,20984,20985,20986,20987,20988,20989,20990,20991,20992,20993,20994,20995,20996,20997,20998,20999,21000,21001,21002,21003,21004,21005,21006,21007,21008,21009,21010,21011,21012,21013,21014,21015,21016,21017,21018,21019,21020,21021,21022,21023,21024,21025,21026,21027,21028,21029,21030,21031,21032,21033,21034,21035,21036,21037,21038,21039,21040,21041,21042,21043,21044,21045,21046,21047,21048,21049,21050,21051,21052,21053,21054,21055,21056,21057,21058,21059,21060,21061,21062,21063,21064,21065,21067]

def refs126 : List ℕ := [21068,21069,21070,21071,21072,21073,21074,21075,21076,21077,21078,21079,21080,21081,21082,21083,21084,21085,21086,21087,21088,21089,21090,21091,21092,21093,21094,21095,21096,21097,21098,21099,21100,21101,21102,21103,21104,21105,21106,21107,21108,21109,21110,21111,21112,21113,21114,21115,21116,21117,21118,21119,21120,21121,21122,21123,21124,21125,21126,21127,21128,21129,21130,21131,21132,21133,21134,21135,21136,21137,21138,21139,21140,21141,21142,21143,21144,21145,21146,21147,21148,21149,21150,21151,21152,21153,21154,21155,21156,21157,21158,21159,21160,21161,21162,21163,21164,21165,21166,21167,21168,21169,21170,21171,21172,21173,21174,21175,21176,21177,21178,21179,21180,21181,21182,21183,21184,21185,21186,21187,21188,21189,21190,21191,21192,21193,21194,21196,21198,21200,21202,21204,21206,21208,21210]

def refs127 : List ℕ := [21211,21212,21213,21214,21215,21216,21217,21218,21219,21220,21221,21222,21223,21224,21225,21226,21227,21228,21229,21230,21231,21232,21233,21234,21235,21236,21237,21238,21239,21240,21241,21242,21243,21244,21245,21246,21247,21248,21249,21250,21251,21252,21253,21254,21255,21256,21257,21258,21259,21260,21261,21262,21263,21264,21265,21266,21267,21268,21269,21270,21271,21272,21273,21274,21275,21276,21277,21278,21279,21280,21281,21282,21283,21284,21285,21286,21287,21288,21289,21290,21291,21292,21293,21294,21295,21296,21297,21298,21299,21300,21301,21302,21303,21304,21305,21306,21307,21308,21309,21310,21311,21312,21313,21314,21315,21316,21317,21318,21319,21320,21321,21322,21323,21324,21325,21326,21327,21328,21329,21330,21331,21332,21333,21334,21335,21336,21337,21338,21339,21340,21341,21342,21343,21344,21345]

def refs128 : List ℕ := [21346,21347,21348,21349,21350,21351,21352,21353,21354,21355,21356,21357,21358,21359,21360,21361,21362,21363,21364,21365,21366,21367,21368,21369,21370,21371,21372,21373,21374,21375,21376,21377,21378,21379,21380,21381,21382,21383,21384,21385,21386,21387,21388,21389,21390,21391,21392,21393,21394,21395,21396,21397,21398,21399,21400,21401,21402,21403,21404,21405,21406,21407,21408,21409,21410,21411,21412,21413,21414,21415,21416,21417,21418,21419,21420,21421,21422,21423,21424,21425,21426,21427,21428,21429,21430,21431,21432,21433,21434,21435,21436,21437,21438,21439,21440,21441,21442,21443,21444,21445,21446,21447,21448,21449,21450,21451,21452,21453,21454,21455,21456,21457,21458,21459,21460,21461,21462,21463,21464,21465,21466,21467,21468,21469,21470,21471,21472,21473,21474,21475,21476,21477,21478,21479,21480]

def refs129 : List ℕ := [21481,21482,21483,21484,21485,21486,21487,21488,21489,21490,21491,21492,21493,21494,21495,21496,21497,21498,21499,21500,21501,21502,21503,21504,21505,21506,21507,21508,21509,21510,21511,21512,21513,21514,21515,21516,21517,21518,21519,21520,21521,21522,21523,21524,21525,21526,21527,21528,21529,21530,21531,21532,21533,21534,21535,21536,21537,21538,21539,21540,21541,21542,21543,21544,21545,21546,21547,21548,21549,21550,21551,21552,21553,21554,21555,21556,21557,21558,21559,21560,21561,21562,21563,21564,21565,21566,21567,21568,21569,21570,21571,21572,21573,21574,21575,21576,21577,21578,21579,21580,21581,21582,21583,21584,21585,21586,21587,21588,21589,21590,21591,21592,21593,21594,21595,21596,21597,21598,21599,21600,21601,21602,21603,21604,21605,21606,21607,21608,21609,21610,21611,21612,21613,21614,21615]

def refs130 : List ℕ := [21616,21617,21618,21619,21620,21621,21622,21623,21624,21625,21626,21627,21628,21629,21630,21631,21632,21633,21634,21635,21636,21637,21638,21639,21640,21641,21642,21643,21644,21645,21646,21647,21648,21649,21650,21651,21652,21653,21654,21655,21656,21657,21658,21659,21660,21661,21662,21663,21664,21665,21666,21667,21668,21669,21670,21671,21672,21673,21674,21675,21676,21677,21678,21679,21680,21681,21682,21683,21684,21685,21686,21687,21688,21689,21690,21691,21692,21693,21694,21695,21696,21697,21698,21699,21700,21701,21702,21703,21704,21705,21706,21707,21708,21709,21710,21711,21712,21713,21714,21715,21716,21717,21718,21719,21720,21721,21722,21723,21724,21725,21726,21727,21728,21729,21730,21731,21732,21733,21734,21735,21736,21737,21738,21739,21740,21741,21742,21743,21744,21745,21746,21747,21748,21749,21750]

def refs131 : List ℕ := [21751,21752,21753,21754,21755,21756,21757,21758,21759,21760,21761,21762,21763,21764,21765,21766,21767,21768,21769,21770,21771,21772,21773,21774,21775,21776,21777,21778,21779,21780,21781,21782,21783,21784,21785,21786,21787,21788,21789,21790,21791,21792,21793,21794,21795,21796,21797,21798,21799,21800,21801,21802,21803,21804,21805,21806,21807,21808,21809,21810,21811,21812,21813,21814,21815,21816,21817,21818,21819,21820,21821,21822,21823,21824,21825,21826,21827,21828,21829,21830,21831,21832,21833,21834,21835,21836,21837,21838,21839,21840,21841,21842,21843,21844,21845,21846,21847,21848,21849,21850,21851,21852,21853,21854,21855,21856,21857,21858,21859,21860,21861,21862,21863,21864,21865,21866,21867,21868,21869,21870,21871,21872,21873,21874,21875,21876,21877,21878,21879,21880,21881,21882,21883,21884,21885]

def refs132 : List ℕ := [21886,21887,21888,21889,21890,21891,21892,21893,21894,21895,21896,21897,21898,21899,21900,21901,21902,21903,21904,21905,21906,21907,21908,21909,21910,21911,21912,21913,21914,21915,21916,21917,21918,21919,21920,21921,21922,21923,21924,21925,21926,21927,21928,21929,21930,21931,21932,21933,21934,21935,21936,21937,21938,21939,21940,21941,21942,21943,21944,21945,21946,21947,21948,21949,21950,21951,21952,21953,21954,21955,21956,21957,21958,21959,21960,21961,21962,21963,21964,21965,21966,21967,21968,21969,21970,21971,21972,21973,21974,21975,21976,21977,21978,21979,21980,21981,21982,21983,21984,21985,21986,21987,21988,21989,21990,21991,21992,21993,21994,21995,21996,21997,21998,21999,22000,22001,22002,22003,22004,22005,22006,22007,22008,22009,22010,22011,22012,22013,22014,22015,22016,22017,22018,22019,22020]

def refs133 : List ℕ := [22021,22022,22023,22024,22025,22026,22027,22028,22029,22030,22031,22032,22033,22034,22035,22036,22037,22038,22039,22040,22041,22042,22043,22044,22045,22046,22047,22048,22049,22050,22051,22052,22053,22054,22055,22056,22057,22058,22059,22060,22061,22062,22063,22064,22065,22066,22067,22068,22069,22070,22071,22072,22073,22074,22075,22076,22077,22078,22079,22080,22081,22082,22083,22084,22085,22086,22087,22088,22089,22090,22091,22092,22093,22094,22095,22096,22097,22098,22099,22100,22101,22102,22103,22104,22105,22106,22107,22108,22109,22110,22111,22112,22113,22114,22115,22116,22117,22118,22119,22120,22121,22122,22123,22124,22125,22126,22127,22128,22129,22130,22131,22132,22133,22134,22135,22136,22137,22138,22139,22140,22141,22142,22143,22144,22145,22146,22147,22148,22149,22150,22151,22152,22153,22154,22156]

def refs134 : List ℕ := [22157,22158,22159,22160,22161,22162,22163,22164,22165,22166,22167,22168,22169,22170,22171,22172,22173,22174,22175,22176,22177,22178,22179,22180,22181,22182,22183,22184,22185,22186,22187,22188,22189,22190,22191,22192,22193,22194,22195,22196,22197,22198,22199,22200,22201,22202,22203,22204,22205,22206,22207,22208,22209,22210,22211,22212,22213,22214,22215,22216,22217,22218,22219,22220,22221,22222,22223,22224,22225,22226,22227,22228,22229,22230,22231,22232,22233,22234,22235,22236,22237,22238,22239,22240,22241,22242,22243,22244,22245,22246,22247,22248,22249,22250,22251,22252,22253,22254,22255,22256,22257,22258,22259,22260,22261,22262,22263,22264,22265,22266,22267,22268,22269,22270,22271,22272,22273,22274,22275,22276,22277,22278,22279,22280,22281,22282,22283,22284,22285,22286,22287,22288,22289,22290,22291]

end HSTZ.TauCetiFinite.D14

   M S B A M L   `   `   `  ����  UI$    UI.ManagerWindows.OverviewPage   5      \ XPresentationFramework, Version=4.0.0.0, Culture=neutral, PublicKeyToken=31bf3856ad364e35R NWindowsBase, Version=4.0.0.0, Culture=neutral, PublicKeyToken=31bf3856ad364e35W SPresentationCore, Version=4.0.0.0, Culture=neutral, PublicKeyToken=31bf3856ad364e35D 9http://schemas.microsoft.com/winfx/2006/xaml/presentation    5      R NSystem.Xaml, Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089:x,http://schemas.microsoft.com/winfx/2006/xaml     5      Jmc;http://schemas.openxmlformats.org/markup-compatibility/2006     5      @d2http://schemas.microsoft.com/expression/blend/2008     5        N� Title$  OverviewPage��5      $	��401��6-   $	��607��6:   .��5      �  � ColumnDefinitions 5   
   �� 5	      $
��522* �6   �� 5
      $	��85* �6   .+�5   
   &   System.Windows.Controls.DataGrid  -   5        $��stationGrid��5   j      AutoGenerateColumns .  $	��263��6/   $
��Left=�6<   $��	32,43,0,0q�6W   $	��Top=�6}   $	��533��6�      CanUserDeleteRows .     CanUserReorderColumns .     CanUserResizeColumns .     CanUserResizeRows .     CanUserSortColumns .     CanUserAddRows .  $��2��6B  	   Columns	 5      4  .System.Windows.Controls.DataGridTemplateColumn  5      ,  &System.Windows.Controls.DataGridColumn
   Header$
 
IP Adresse��6)      Width5  /System.Windows.Controls.DataGridLengthConverter$ * 6=      
IsReadOnly .    CellTemplate 5      �� 5      .R�5      ��  �� TextAlignment$ Center=�6B   ��6(   �� *
IpAdress+6B   5      5        5      $
 
Tilsluttet��6)   $ * 6=    .  5      �� 5      .R�5      �� $��Center=�6G   $��Center=�6d   {�.   d� 	IsChecked 6'   �� *	Connected+6   5      5      5      �� 5    
   $��32,325,12,12q�6    �� Orientation$ 
Horizontal=�6+   $��2��6D   .+�5!      �� -   5        $��RefreshButton��5!   I   $��Opdater��6   $��20,20,10,20q�6(   $��23��6=   $��75��6^   6i   �� 5"      -   5        $��
BackButton��5"   I   $��Tilbage��6   $��20,20,10,20q�6(   $��23��6=   $��75��6[   6f   �� 5#      -   5        $��	AddButton��5#   G   $��Tilføj��6   $��20,20,10,20q�6&   $��23��6;   $��75��6X   6c   �� 5$      -   5        $��RemoveButton��5$   F   $��Fjern��6   $��20,20,10,20q�6%   $��23��6:   $��75��6Z   6e   �� 5%      -   5        $��StartEndElectionButton��5%   K   $��
Start Valg��6   $��20,20,10,20q�6*   $��23��6?   $��98��6i   6t   5&      �� 5'   
   -   5        $��PasswordLabel��5'   U   $�� ��6   $��28��6   $
��Left=�6'   $��	32,12,0,0q�6B   $	��Top=�6j   $	��426��6�   �� 5(   
   -   5        $��UpdateLabel��5(   U   $�� ��6   $��28��6   $
��Left=�6'   $��	464,0,0,0q�6B   $	��Top=�6h   $	��101��6�   $��2��6�   � 5)   
   -	   5        $��
LoadingBar��5)   P   $��9��6   $
��Left=�6!   $��
465,31,0,0q�6<   $	��Top=�6b   $	��100��6z   $��2��6�   5*      5+      